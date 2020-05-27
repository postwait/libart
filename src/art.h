#include <stdint.h>
#include <unistd.h>
#include <stdbool.h>
#ifndef ART_H
#define ART_H

#ifdef __cplusplus
extern "C" {
#endif

#define NODE4   1
#define NODE16  2
#define NODE48  3
#define NODE256 4
#define ART_SER_COMPLETE 1
#define ART_SER_HDR_LEN  8

#define MAX_PREFIX_LEN 10

#if defined(__GNUC__) && !defined(__clang__)
# if __STDC_VERSION__ >= 199901L && 402 == (__GNUC__ * 100 + __GNUC_MINOR__)
/*
 * GCC 4.2.2's C99 inline keyword support is pretty broken; avoid. Introduced in
 * GCC 4.2.something, fixed in 4.3.0. So checking for specific major.minor of
 * 4.2 is fine.
 */
#  define BROKEN_GCC_C99_INLINE
# endif
#endif

typedef int(*art_callback)(void *data, const unsigned char *key, uint32_t key_len, void *value);

/**
 * This struct is included as part
 * of all the various node sizes
 */
typedef struct {
    uint32_t partial_len;
    uint8_t type;
    uint8_t num_children;
    unsigned char partial[MAX_PREFIX_LEN];
} art_node;

/**
 * This is a pointer-invariant stub for type-safety
 */
typedef struct art_pin art_pin;

/**
 * Small node with only 4 children
 */
typedef struct {
    art_node n;
    unsigned char keys[4];
    art_pin *children[4];
} art_node4;

/**
 * Node with 16 children
 */
typedef struct {
    art_node n;
    unsigned char keys[16];
    art_pin *children[16];
} art_node16;

/**
 * Node with 48 children, but
 * a full 256 byte field.
 */
typedef struct {
    art_node n;
    unsigned char keys[256];
    art_pin *children[48];
} art_node48;

/**
 * Full node with 256 children
 */
typedef struct {
    art_node n;
    art_pin *children[256];
} art_node256;

/**
 * Represents a leaf. These are
 * of arbitrary size, as they include the key.
 */
typedef struct {
    void *value;
    uint32_t key_len;
    unsigned char key[];
} art_leaf;

typedef struct art_tree art_tree;

typedef struct file_serializer {
  int fd;
  size_t offset;
  uintptr_t base;
  bool mapped;
} file_serializer_t;

typedef void *  (*art_alloc_f)(void *closure, const art_tree *, size_t);
typedef void    (*art_free_f)(void *closure, const art_tree *, void *);
typedef ssize_t (*art_value_serialize_f)(void *closure, const art_tree *t, void *value,
                                         uint64_t (*writef)(file_serializer_t *, const void *tgt, size_t tgt_len), file_serializer_t *);
typedef void *  (*art_value_deserialize_f)(void *closure, const art_tree *t, const void *src);
typedef void    (*art_value_release_f)(void *closure, const art_tree *t, void *value);

typedef struct {
    art_value_serialize_f serialize;
    art_value_deserialize_f deserialize;
    art_value_release_f release;
    art_alloc_f alloc;
    art_free_f free;
    bool read_only;
} art_tree_interposition_t;

/**
 * Main struct, points to root.
 */
struct art_tree {
    art_pin                  *root;       /* The root of the tree (relative to base) */
    uint64_t                  size;       /* number of elements in the tree */
    file_serializer_t        *ser;
    art_tree_interposition_t *ops;        /* operations */
    void *ops_closure;
};

/**
 * Initializes an ART tree
 * @return 0 on success.
 */
int art_tree_init(art_tree *t);

/**
 * DEPRECATED
 * Initializes an ART tree
 * @return 0 on success.
 */
#define init_art_tree(...) art_tree_init(__VA_ARGS__)

/**
 * Sets interposition operations for an ART
 * @arg t The tree
 * @arg ser An alternative serializer
 * @arg ops Interposition operations
 * @arg closure Closure for interposer
 */
void art_tree_interpose(art_tree *t, file_serializer_t *, art_tree_interposition_t *ops, void *closure);

/**
 * Destroys an ART tree
 * @return 0 on success.
 */
int art_tree_destroy(art_tree *t);

/**
 * DEPRECATED
 * Initializes an ART tree
 * @return 0 on success.
 */
#define destroy_art_tree(...) art_tree_destroy(__VA_ARGS__)

/**
 * Returns the size of the ART tree.
 */
#ifdef BROKEN_GCC_C99_INLINE
# define art_size(t) ((t)->size)
#else
inline uint64_t art_size(art_tree *t) {
    return t->size;
}
#endif

/**
 * inserts a new value into the art tree
 * @arg t the tree
 * @arg key the key
 * @arg key_len the length of the key
 * @arg value opaque value.
 * @return null if the item was newly inserted, otherwise
 * the old value pointer is returned.
 */
void* art_insert(art_tree *t, const unsigned char *key, int key_len, void *value);

/**
 * inserts a new value into the art tree (not replacing)
 * @arg t the tree
 * @arg key the key
 * @arg key_len the length of the key
 * @arg value opaque value.
 * @return null if the item was newly inserted, otherwise
 * the old value pointer is returned.
 */
void* art_insert_no_replace(art_tree *t, const unsigned char *key, int key_len, void *value);

/**
 * Deletes a value from the ART tree
 * @arg t The tree
 * @arg key The key
 * @arg key_len The length of the key
 * @return NULL if the item was not found, otherwise
 * the value pointer is returned.
 */
void* art_delete(art_tree *t, const unsigned char *key, int key_len);

/**
 * Searches for a value in the ART tree
 * @arg t The tree
 * @arg key The key
 * @arg key_len The length of the key
 * @return NULL if the item was not found, otherwise
 * the value pointer is returned.
 */
void* art_search(const art_tree *t, const unsigned char *key, int key_len);

/**
 * Releases a value returned from search back into the ART tree
 * @arg t The tree
 * @arg value A value returned from art_search()
 */
void art_release(const art_tree *t, void *value);

/**
 * Returns the minimum valued leaf
 * @return The minimum leaf or NULL
 */
art_leaf* art_minimum(art_tree *t);

/**
 * Returns the maximum valued leaf
 * @return The maximum leaf or NULL
 */
art_leaf* art_maximum(art_tree *t);

/**
 * Iterates through the entries pairs in the map,
 * invoking a callback for each. The call back gets a
 * key, value for each and returns an integer stop value.
 * If the callback returns non-zero, then the iteration stops.
 * @arg t The tree to iterate over
 * @arg cb The callback function to invoke
 * @arg data Opaque handle passed to the callback
 * @return 0 on success, or the return of the callback.
 */
int art_iter(art_tree *t, art_callback cb, void *data);

/**
 * Iterates through the entries pairs in the map,
 * invoking a callback for each that matches a given prefix.
 * The call back gets a key, value for each and returns an integer stop value.
 * If the callback returns non-zero, then the iteration stops.
 * @arg t The tree to iterate over
 * @arg prefix The prefix of keys to read
 * @arg prefix_len The length of the prefix
 * @arg cb The callback function to invoke
 * @arg data Opaque handle passed to the callback
 * @return 0 on success, or the return of the callback.
 */
int art_iter_prefix(art_tree *t, const unsigned char *prefix, int prefix_len, art_callback cb, void *data);

file_serializer_t *art_serializer_new(const char *file, bool create);
bool art_serializer_finalize(file_serializer_t *ser, uint32_t flags);
void art_serializer_destroy(file_serializer_t *ser);

const void *art_serializer_offset_to_address(file_serializer_t *, uintptr_t offset);

#define ART_DEFAULT_OFFSET 8
bool art_serializer_write_tree(file_serializer_t *, const art_tree *in, art_tree_interposition_t *ops, void *closure, size_t *offset);
bool art_serializer_tree_at_offset(file_serializer_t *, art_tree *dt, size_t offset, art_tree_interposition_t *ops, void *closure);
uintptr_t art_serializer_write_custom(file_serializer_t *ser, const void *b, size_t l);

#ifdef __cplusplus
}
#endif

#endif
