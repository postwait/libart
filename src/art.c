#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <stdio.h>
#include <assert.h>
#include <unistd.h>
#include <sys/uio.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/mman.h>
#include "art.h"

#ifdef __i386__
    #include <emmintrin.h>
#else
#ifdef __amd64__
    #include <emmintrin.h>
#endif
#endif

struct art_ser_hdr {
    unsigned char hdr_ver[4];
    uint16_t version;
    uint16_t flags;
};

const struct art_ser_hdr ART_SER_HDR = {
  .hdr_ver = { 'A', 'R', 'T', '\0' },
  .version = 0,
  .flags = 0
};

#define ART_SER_FLAGS_OFFSET 6

struct file_serializer self_image_ser = {
  .fd = -1,
  .offset = 0,
  .base = 0,
};

/**
 * Macros to manipulate pointer tags
 */
#define WRITEALIGN 8
#define MAX_ON_STACK (1<<16)
#define IS_LEAF(x) (((uintptr_t)x & 1))
#define SET_LEAF(x) ((void*)((uintptr_t)x | 1))
#define LEAF_RAW(x) ((art_leaf*)((void*)((uintptr_t)x & ~1)))
static inline art_node *PIN_2_NODE(const art_tree *t, art_pin *x) {
    return ( x ? ((art_node *)((uintptr_t)x + t->ser->base)) : (art_node *)NULL );
}
static inline void *PIN_2_PTR(const art_tree *t, art_pin *x) {
    return ( x ? ((art_node *)((uintptr_t)x + t->ser->base)) : (art_node *)NULL );
}
static inline art_pin *NODE_2_PIN(const art_tree *t, art_node *x) {
    return ( x ? ((art_pin *)((uintptr_t)x - t->ser->base)) : (art_pin *)NULL );
}

static void *art_default_alloc(void *c, const art_tree *t, size_t l) {
    (void)c;
    (void)t;
    return malloc(l);
}
static void art_default_free(void *c, const art_tree *t, void *v) {
    (void)c;
    (void)t;
    free(v);
}

static art_tree_interposition_t art_tree_default_interposition = {
    .read_only = false,
    .alloc = art_default_alloc,
    .free = art_default_free
};

typedef struct art_pin art_pin;
/**
 * Allocates a node of the given type,
 * initializes to zero and sets the type.
 */
static art_node* alloc_node(const art_tree *t, uint8_t type) {
    art_node* n;
    size_t alloc_size = 0;
    switch (type) {
        case NODE4:
            alloc_size = sizeof(art_node4);
            break;
        case NODE16:
            alloc_size = sizeof(art_node16);
            break;
        case NODE48:
            alloc_size = sizeof(art_node48);
            break;
        case NODE256:
            alloc_size = sizeof(art_node256);
            break;
        default:
            abort();
    }
    n = (art_node *)t->ops->alloc(t->ops_closure, t, alloc_size);
    memset(n, 0, alloc_size);
    n->type = type;
    return n;
}

/**
 * Initializes an ART tree
 * @return 0 on success.
 */
int art_tree_init(art_tree *t) {
    memset(t, 0, sizeof(*t));
    t->ops = &art_tree_default_interposition;
    t->ser = &self_image_ser;
    return 0;
}

void art_tree_interpose(art_tree *t, file_serializer_t *ser, art_tree_interposition_t *ops, void *c) {
    assert(t->size == 0);
    t->ser = ser ? ser : &self_image_ser;
    t->ops = ops;
    t->ops_closure = c;
}

// Recursively destroys the tree
static void destroy_node(const art_tree *t, art_node *n) {
    // Break if null
    if (!n) return;

    // Special case leafs
    if (IS_LEAF(n)) {
        t->ops->free(t->ops_closure, t, LEAF_RAW(n));
        return;
    }

    // Handle each node type
    int i, idx;
    union {
        art_node4 *p1;
        art_node16 *p2;
        art_node48 *p3;
        art_node256 *p4;
    } p;
    switch (n->type) {
        case NODE4:
            p.p1 = (art_node4*)n;
            for (i=0;i<n->num_children;i++) {
                destroy_node(t, PIN_2_NODE(t, p.p1->children[i]));
            }
            break;

        case NODE16:
            p.p2 = (art_node16*)n;
            for (i=0;i<n->num_children;i++) {
                destroy_node(t, PIN_2_NODE(t, p.p2->children[i]));
            }
            break;

        case NODE48:
            p.p3 = (art_node48*)n;
            for (i=0;i<256;i++) {
                idx = ((art_node48*)n)->keys[i]; 
                if (!idx) continue; 
                destroy_node(t, PIN_2_NODE(t, p.p3->children[idx-1]));
            }
            break;

        case NODE256:
            p.p4 = (art_node256*)n;
            for (i=0;i<256;i++) {
                if (p.p4->children[i])
                    destroy_node(t, PIN_2_NODE(t, p.p4->children[i]));
            }
            break;

        default:
            abort();
    }

    // Free ourself on the way up
    t->ops->free(t->ops_closure, t, n);
}

/**
 * Destroys an ART tree
 * @return 0 on success.
 */
int art_tree_destroy(art_tree *t) {
    destroy_node(t, PIN_2_NODE(t, t->root));
    return 0;
}

/**
 * Returns the size of the ART tree.
 */

#ifndef BROKEN_GCC_C99_INLINE
extern inline uint64_t art_size(art_tree *t);
#endif

static art_pin** find_child(art_node *n, unsigned char c) {
    int i, mask, bitfield;
    union {
        art_node4 *p1;
        art_node16 *p2;
        art_node48 *p3;
        art_node256 *p4;
    } p;
    switch (n->type) {
        case NODE4:
            p.p1 = (art_node4*)n;
            for (i=0 ; i < n->num_children; i++) {
		/* this cast works around a bug in gcc 5.1 when unrolling loops
		 * https://gcc.gnu.org/bugzilla/show_bug.cgi?id=59124
		 */
                if (((unsigned char*)p.p1->keys)[i] == c)
                    return &p.p1->children[i];
            }
            break;

        {
        case NODE16:
            p.p2 = (art_node16*)n;

            // support non-86 architectures
            #ifdef __i386__
                // Compare the key to all 16 stored keys
                __m128i cmp;
                cmp = _mm_cmpeq_epi8(_mm_set1_epi8(c),
                        _mm_loadu_si128((__m128i*)p.p2->keys));
                
                // Use a mask to ignore children that don't exist
                mask = (1 << n->num_children) - 1;
                bitfield = _mm_movemask_epi8(cmp) & mask;
            #else
            #ifdef __amd64__
                // Compare the key to all 16 stored keys
                __m128i cmp;
                cmp = _mm_cmpeq_epi8(_mm_set1_epi8(c),
                        _mm_loadu_si128((__m128i*)p.p2->keys));

                // Use a mask to ignore children that don't exist
                mask = (1 << n->num_children) - 1;
                bitfield = _mm_movemask_epi8(cmp) & mask;
            #else
                // Compare the key to all 16 stored keys
                bitfield = 0;
                for (i = 0; i < 16; ++i) {
                    if (p.p2->keys[i] == c)
                        bitfield |= (1 << i);
                }

                // Use a mask to ignore children that don't exist
                mask = (1 << n->num_children) - 1;
                bitfield &= mask;
            #endif
            #endif

            /*
             * If we have a match (any bit set) then we can
             * return the pointer match using ctz to get
             * the index.
             */
            if (bitfield)
                return &p.p2->children[__builtin_ctz(bitfield)];
            break;
        }

        case NODE48:
            p.p3 = (art_node48*)n;
            i = p.p3->keys[c];
            if (i)
                return &p.p3->children[i-1];
            break;

        case NODE256:
            p.p4 = (art_node256*)n;
            if (p.p4->children[c])
                return &p.p4->children[c];
            break;

        default:
            abort();
    }
    return NULL;
}

// Simple inlined if
static inline int min(int a, int b) {
    return (a < b) ? a : b;
}

/**
 * Returns the number of prefix characters shared between
 * the key and node.
 */
static int check_prefix(const art_node *n, const unsigned char *key, int key_len, int depth) {
    int max_cmp = min(min(n->partial_len, MAX_PREFIX_LEN), key_len - depth);
    int idx;
    for (idx=0; idx < max_cmp; idx++) {
        if (n->partial[idx] != key[depth+idx])
            return idx;
    }
    return idx;
}

/**
 * Checks if a leaf matches
 * @return 0 on success.
 */
static int leaf_matches(const art_leaf *n, const unsigned char *key, int key_len, int depth) {
    (void)depth;
    // Fail if the key lengths are different
    if (n->key_len != (uint32_t)key_len) return 1;

    // Compare the keys starting at the depth
    return memcmp(n->key, key, key_len);
}

void art_release(const art_tree *t, void *v) {
    if(t->ops->release) t->ops->release(t->ops_closure, t, v);
}
/**
 * Searches for a value in the ART tree
 * @arg t The tree
 * @arg key The key
 * @arg key_len The length of the key
 * @return NULL if the item was not found, otherwise
 * the value pointer is returned.
 */
void* art_search(const art_tree *t, const unsigned char *key, int key_len) {
    art_pin **child_pin;
    art_node *n = PIN_2_NODE(t, t->root);
    int prefix_len, depth = 0;
    while (n) {
        // Might be a leaf
        if (IS_LEAF(n)) {
            n = (art_node*)LEAF_RAW(n);
            // Check if the expanded path matches
            if (!leaf_matches((art_leaf*)n, key, key_len, depth)) {
                if(t->ops->deserialize)
                  return t->ops->deserialize(t->ops_closure, t, PIN_2_PTR(t, ((art_leaf*)n)->value));
                return ((art_leaf*)n)->value;
            }
            return NULL;
        }

        // Bail if the prefix does not match
        if (n->partial_len) {
            prefix_len = check_prefix(n, key, key_len, depth);
            if (prefix_len != min(MAX_PREFIX_LEN, n->partial_len))
                return NULL;
            depth = depth + n->partial_len;
        }

        // Recursively search
        child_pin = find_child(n, key[depth]);
        n = (child_pin) ? PIN_2_NODE(t, *child_pin) : NULL;
        depth++;
    }
    return NULL;
}

// Find the minimum leaf under a node
static art_leaf* minimum(const art_tree *t, const art_node *n) {
    // Handle base cases
    if (!n) return NULL;
    if (IS_LEAF(n)) return LEAF_RAW(n);

    int idx;
    switch (n->type) {
        case NODE4:
            return minimum(t, PIN_2_NODE(t, ((const art_node4*)n)->children[0]));
        case NODE16:
            return minimum(t, PIN_2_NODE(t, ((const art_node16*)n)->children[0]));
        case NODE48:
            idx=0;
            while (!((const art_node48*)n)->keys[idx]) idx++;
            idx = ((const art_node48*)n)->keys[idx] - 1;
            return minimum(t, PIN_2_NODE(t, ((const art_node48*)n)->children[idx]));
        case NODE256:
            idx=0;
            while (!((const art_node256*)n)->children[idx]) idx++;
            return minimum(t, PIN_2_NODE(t, ((const art_node256*)n)->children[idx]));
        default:
            abort();
    }
}

// Find the maximum leaf under a node
static art_leaf* maximum(const art_tree *t, const art_node *n) {
    // Handle base cases
    if (!n) return NULL;
    if (IS_LEAF(n)) return LEAF_RAW(n);

    int idx;
    switch (n->type) {
        case NODE4:
            return maximum(t, PIN_2_NODE(t, ((const art_node4*)n)->children[n->num_children-1]));
        case NODE16:
            return maximum(t, PIN_2_NODE(t, ((const art_node16*)n)->children[n->num_children-1]));
        case NODE48:
            idx=255;
            while (!((const art_node48*)n)->keys[idx]) idx--;
            idx = ((const art_node48*)n)->keys[idx] - 1;
            return maximum(t, PIN_2_NODE(t, ((const art_node48*)n)->children[idx]));
        case NODE256:
            idx=255;
            while (!((const art_node256*)n)->children[idx]) idx--;
            return maximum(t, PIN_2_NODE(t, ((const art_node256*)n)->children[idx]));
        default:
            abort();
    }
}

/**
 * Returns the minimum valued leaf
 */
art_leaf* art_minimum(art_tree *t) {
    return minimum(t, PIN_2_NODE(t, t->root));
}

/**
 * Returns the maximum valued leaf
 */
art_leaf* art_maximum(art_tree *t) {
    return maximum(t, PIN_2_NODE(t, t->root));
}

static art_leaf* make_leaf(const art_tree *t, const unsigned char *key, int key_len, void *value) {
    art_leaf *l = (art_leaf*)t->ops->alloc(t->ops_closure, t, sizeof(art_leaf)+key_len);
    memset(l, 0, sizeof(art_leaf)+key_len);
    l->value = value;
    l->key_len = key_len;
    memcpy(l->key, key, key_len);
    return l;
}

static int longest_common_prefix(art_leaf *l1, art_leaf *l2, int depth) {
    int max_cmp = min(l1->key_len, l2->key_len) - depth;
    int idx;
    for (idx=0; idx < max_cmp; idx++) {
        if (l1->key[depth+idx] != l2->key[depth+idx])
            return idx;
    }
    return idx;
}

static void copy_header(art_node *dest, art_node *src) {
    dest->num_children = src->num_children;
    dest->partial_len = src->partial_len;
    memcpy(dest->partial, src->partial, min(MAX_PREFIX_LEN, src->partial_len));
}

static void add_child256(const art_tree *t, art_node256 *n, art_pin **ref, unsigned char c, void *child) {
    (void)ref;
    n->n.num_children++;
    n->children[c] = NODE_2_PIN(t, child);
}

static void add_child48(const art_tree *t, art_node48 *n, art_pin **ref, unsigned char c, void *child) {
    if (n->n.num_children < 48) {
        int pos = 0;
        while (n->children[pos]) pos++;
        n->children[pos] = NODE_2_PIN(t, child);
        n->keys[c] = pos + 1;
        n->n.num_children++;
    } else {
        art_node256 *new_node = (art_node256*)alloc_node(t, NODE256);
        for (int i=0;i<256;i++) {
            if (n->keys[i]) {
                new_node->children[i] = n->children[n->keys[i] - 1];
            }
        }
        copy_header((art_node*)new_node, (art_node*)n);
        *ref = NODE_2_PIN(t, (art_node*)new_node);
        t->ops->free(t->ops_closure, t, n);
        add_child256(t, new_node, ref, c, child);
    }
}

static void add_child16(const art_tree *t, art_node16 *n, art_pin **ref, unsigned char c, void *child) {
    if (n->n.num_children < 16) {
        unsigned mask = (1 << n->n.num_children) - 1;
        
        // support non-x86 architectures
        #ifdef __i386__
            __m128i cmp;

            // Compare the key to all 16 stored keys
            cmp = _mm_cmplt_epi8(_mm_set1_epi8(c),
                    _mm_loadu_si128((__m128i*)n->keys));

            // Use a mask to ignore children that don't exist
            unsigned bitfield = _mm_movemask_epi8(cmp) & mask;
        #else
        #ifdef __amd64__
            __m128i cmp;

            // Compare the key to all 16 stored keys
            cmp = _mm_cmplt_epi8(_mm_set1_epi8(c),
                    _mm_loadu_si128((__m128i*)n->keys));

            // Use a mask to ignore children that don't exist
            unsigned bitfield = _mm_movemask_epi8(cmp) & mask;
        #else
            // Compare the key to all 16 stored keys
            unsigned bitfield = 0;
            for (short i = 0; i < 16; ++i) {
                if (c < n->keys[i])
                    bitfield |= (1 << i);
            }

            // Use a mask to ignore children that don't exist
            bitfield &= mask;    
        #endif
        #endif

        // Check if less than any
        unsigned idx;
        if (bitfield) {
            idx = __builtin_ctz(bitfield);
            memmove(n->keys+idx+1,n->keys+idx,n->n.num_children-idx);
            memmove(n->children+idx+1,n->children+idx,
                    (n->n.num_children-idx)*sizeof(void*));
        } else
            idx = n->n.num_children;

        // Set the child
        n->keys[idx] = c;
        n->children[idx] = NODE_2_PIN(t, (art_node*)child);
        n->n.num_children++;

    } else {
        art_node48 *new_node = (art_node48*)alloc_node(t, NODE48);

        // Copy the child pointers and populate the key map
        memcpy(new_node->children, n->children,
                sizeof(void*)*n->n.num_children);
        for (int i=0;i<n->n.num_children;i++) {
            new_node->keys[n->keys[i]] = i + 1;
        }
        copy_header((art_node*)new_node, (art_node*)n);
        *ref = NODE_2_PIN(t, (art_node*)new_node);
        t->ops->free(t->ops_closure, t, n);
        add_child48(t, new_node, ref, c, child);
    }
}

static void add_child4(const art_tree *t, art_node4 *n, art_pin **ref, unsigned char c, void *child) {
    if (n->n.num_children < 4) {
        int idx;
        for (idx=0; idx < n->n.num_children; idx++) {
            if (c < n->keys[idx]) break;
        }

        // Shift to make room
        memmove(n->keys+idx+1, n->keys+idx, n->n.num_children - idx);
        memmove(n->children+idx+1, n->children+idx,
                (n->n.num_children - idx)*sizeof(void*));

        // Insert element
        n->keys[idx] = c;
        n->children[idx] = NODE_2_PIN(t, (art_node*)child);
        n->n.num_children++;

    } else {
        art_node16 *new_node = (art_node16*)alloc_node(t, NODE16);

        // Copy the child pointers and the key map
        memcpy(new_node->children, n->children,
                sizeof(void*)*n->n.num_children);
        memcpy(new_node->keys, n->keys,
                sizeof(unsigned char)*n->n.num_children);
        copy_header((art_node*)new_node, (art_node*)n);
        *ref = NODE_2_PIN(t, (art_node*)new_node);
        t->ops->free(t->ops_closure, t, n);
        add_child16(t, new_node, ref, c, child);
    }
}

static void add_child(const art_tree *t, art_node *n, art_pin **ref, unsigned char c, void *child) {
    switch (n->type) {
        case NODE4:
            return add_child4(t, (art_node4*)n, ref, c, child);
        case NODE16:
            return add_child16(t, (art_node16*)n, ref, c, child);
        case NODE48:
            return add_child48(t, (art_node48*)n, ref, c, child);
        case NODE256:
            return add_child256(t, (art_node256*)n, ref, c, child);
        default:
            abort();
    }
}

/**
 * Calculates the index at which the prefixes mismatch
 */
static int prefix_mismatch(const art_tree *t, const art_node *n, const unsigned char *key, int key_len, int depth) {
    int max_cmp = min(min(MAX_PREFIX_LEN, n->partial_len), key_len - depth);
    int idx;
    for (idx=0; idx < max_cmp; idx++) {
        if (n->partial[idx] != key[depth+idx])
            return idx;
    }

    // If the prefix is short we can avoid finding a leaf
    if (n->partial_len > MAX_PREFIX_LEN) {
        // Prefix is longer than what we've checked, find a leaf
        art_leaf *l = minimum(t, n);
        max_cmp = min(l->key_len, key_len)- depth;
        for (; idx < max_cmp; idx++) {
            if (l->key[idx+depth] != key[depth+idx])
                return idx;
        }
    }
    return idx;
}

static void* recursive_insert(const art_tree *t, art_node *n, art_pin **ref, const unsigned char *key, int key_len, void *value, int depth, int *old, int replace) {
    // If we are at a NULL node, inject a leaf
    if (!n) {
        *ref = NODE_2_PIN(t, (art_node*)SET_LEAF(make_leaf(t, key, key_len, value)));
        return NULL;
    }

    // If we are at a leaf, we need to replace it with a node
    if (IS_LEAF(n)) {
        art_leaf *l = LEAF_RAW(n);

        // Check if we are updating an existing value
        if (!leaf_matches(l, key, key_len, depth)) {
            *old = 1;
            void *old_val = l->value;
            if(replace) l->value = value;
            return old_val;
        }

        // New value, we must split the leaf into a node4
        art_node4 *new_node = (art_node4*)alloc_node(t, NODE4);

        // Create a new leaf
        art_leaf *l2 = make_leaf(t, key, key_len, value);

        // Determine longest prefix
        int longest_prefix = longest_common_prefix(l, l2, depth);
        new_node->n.partial_len = longest_prefix;
        memcpy(new_node->n.partial, key+depth, min(MAX_PREFIX_LEN, longest_prefix));
        // Add the leafs to the new node4
        *ref = NODE_2_PIN(t, (art_node*)new_node);
        add_child4(t, new_node, ref, l->key[depth+longest_prefix], SET_LEAF(l));
        add_child4(t, new_node, ref, l2->key[depth+longest_prefix], SET_LEAF(l2));
        return NULL;
    }

    // Check if given node has a prefix
    if (n->partial_len) {
        // Determine if the prefixes differ, since we need to split
        int prefix_diff = prefix_mismatch(t, n, key, key_len, depth);
        if ((uint32_t)prefix_diff >= n->partial_len) {
            depth += n->partial_len;
            goto RECURSE_SEARCH;
        }

        // Create a new node
        art_node4 *new_node = (art_node4*)alloc_node(t, NODE4);
        *ref = NODE_2_PIN(t, (art_node*)new_node);
        new_node->n.partial_len = prefix_diff;
        memcpy(new_node->n.partial, n->partial, min(MAX_PREFIX_LEN, prefix_diff));

        // Adjust the prefix of the old node
        if (n->partial_len <= MAX_PREFIX_LEN) {
            add_child4(t, new_node, ref, n->partial[prefix_diff], n);
            n->partial_len -= (prefix_diff+1);
            memmove(n->partial, n->partial+prefix_diff+1,
                    min(MAX_PREFIX_LEN, n->partial_len));
        } else {
            n->partial_len -= (prefix_diff+1);
            art_leaf *l = minimum(t, n);
            add_child4(t, new_node, ref, l->key[depth+prefix_diff], n);
            memcpy(n->partial, l->key+depth+prefix_diff+1,
                    min(MAX_PREFIX_LEN, n->partial_len));
        }

        // Insert the new leaf
        art_leaf *l = make_leaf(t, key, key_len, value);
        add_child4(t, new_node, ref, key[depth+prefix_diff], SET_LEAF(l));
        return NULL;
    }

RECURSE_SEARCH:;

    // Find a child to recurse to
    art_pin **child = find_child(n, key[depth]);
    if (child) {
        return recursive_insert(t, PIN_2_NODE(t, *child), child, key, key_len, value, depth+1, old, replace);
    }

    // No child, node goes within us
    art_leaf *l = make_leaf(t, key, key_len, value);
    add_child(t, n, ref, key[depth], SET_LEAF(l));
    return NULL;
}

/**
 * inserts a new value into the art tree
 * @arg t the tree
 * @arg key the key
 * @arg key_len the length of the key
 * @arg value opaque value.
 * @return null if the item was newly inserted, otherwise
 * the old value pointer is returned.
 */
void* art_insert(art_tree *t, const unsigned char *key, int key_len, void *value) {
    int old_val = 0;
    assert(!t->ops || !t->ops->read_only);
    void *old = recursive_insert(t, PIN_2_NODE(t, t->root), &t->root, key, key_len, value, 0, &old_val, 1);
    if (!old_val) t->size++;
    return old;
}

/**
 * inserts a new value into the art tree (no replace)
 * @arg t the tree
 * @arg key the key
 * @arg key_len the length of the key
 * @arg value opaque value.
 * @return null if the item was newly inserted, otherwise
 * the old value pointer is returned.
 */
void* art_insert_no_replace(art_tree *t, const unsigned char *key, int key_len, void *value) {
    int old_val = 0;
    assert(!t->ops || !t->ops->read_only);
    void *old = recursive_insert(t, PIN_2_NODE(t, t->root), &t->root, key, key_len, value, 0, &old_val, 0);
    if (!old_val) t->size++;
    return old;
}

static void remove_child256(const art_tree *t, art_node256 *n, art_pin **ref, unsigned char c) {
    n->children[c] = NULL;
    n->n.num_children--;

    // Resize to a node48 on underflow, not immediately to prevent
    // trashing if we sit on the 48/49 boundary
    if (n->n.num_children == 37) {
        art_node48 *new_node = (art_node48*)alloc_node(t, NODE48);
        *ref = NODE_2_PIN(t, (art_node*)new_node);
        copy_header((art_node*)new_node, (art_node*)n);

        int pos = 0;
        for (int i=0;i<256;i++) {
            if (n->children[i]) {
                new_node->children[pos] = n->children[i];
                new_node->keys[i] = pos + 1;
                pos++;
            }
        }
        t->ops->free(t->ops_closure, t, n);
    }
}

static void remove_child48(const art_tree *t, art_node48 *n, art_pin **ref, unsigned char c) {
    int pos = n->keys[c];
    n->keys[c] = 0;
    n->children[pos-1] = NULL;
    n->n.num_children--;

    if (n->n.num_children == 12) {
        art_node16 *new_node = (art_node16*)alloc_node(t, NODE16);
        *ref = NODE_2_PIN(t, (art_node*)new_node);
        copy_header((art_node*)new_node, (art_node*)n);

        int child = 0;
        for (int i=0;i<256;i++) {
            pos = n->keys[i];
            if (pos) {
                new_node->keys[child] = i;
                new_node->children[child] = n->children[pos - 1];
                child++;
            }
        }
        t->ops->free(t->ops_closure, t, n);
    }
}

static void remove_child16(const art_tree *t, art_node16 *n, art_pin **ref, art_pin **l) {
    int pos = l - n->children;
    memmove(n->keys+pos, n->keys+pos+1, n->n.num_children - 1 - pos);
    memmove(n->children+pos, n->children+pos+1, (n->n.num_children - 1 - pos)*sizeof(void*));
    n->n.num_children--;

    if (n->n.num_children == 3) {
        art_node4 *new_node = (art_node4*)alloc_node(t, NODE4);
        *ref = NODE_2_PIN(t, (art_node*)new_node);
        copy_header((art_node*)new_node, (art_node*)n);
        memcpy(new_node->keys, n->keys, 4);
        memcpy(new_node->children, n->children, 4*sizeof(void*));
        t->ops->free(t->ops_closure, t, n);
    }
}

static void remove_child4(const art_tree *t, art_node4 *n, art_pin **ref, art_pin **l) {
    int pos = l - n->children;
    memmove(n->keys+pos, n->keys+pos+1, n->n.num_children - 1 - pos);
    memmove(n->children+pos, n->children+pos+1, (n->n.num_children - 1 - pos)*sizeof(void*));
    n->n.num_children--;

    // Remove nodes with only a single child
    if (n->n.num_children == 1) {
        art_node *child = PIN_2_NODE(t, n->children[0]);
        if (!IS_LEAF(child)) {
            // Concatenate the prefixes
            int prefix = n->n.partial_len;
            if (prefix < MAX_PREFIX_LEN) {
                n->n.partial[prefix] = n->keys[0];
                prefix++;
            }
            if (prefix < MAX_PREFIX_LEN) {
                int sub_prefix = min(child->partial_len, MAX_PREFIX_LEN - prefix);
                memcpy(n->n.partial+prefix, child->partial, sub_prefix);
                prefix += sub_prefix;
            }

            // Store the prefix in the child
            memcpy(child->partial, n->n.partial, min(prefix, MAX_PREFIX_LEN));
            child->partial_len += n->n.partial_len + 1;
        }
        *ref = NODE_2_PIN(t, child);
        t->ops->free(t->ops_closure, t, n);
    }
}

static void remove_child(const art_tree *t, art_node *n, art_pin **ref, unsigned char c, art_pin **l) {
    switch (n->type) {
        case NODE4:
            return remove_child4(t, (art_node4*)n, ref, l);
        case NODE16:
            return remove_child16(t, (art_node16*)n, ref, l);
        case NODE48:
            return remove_child48(t, (art_node48*)n, ref, c);
        case NODE256:
            return remove_child256(t, (art_node256*)n, ref, c);
        default:
            abort();
    }
}

static art_leaf* recursive_delete(const art_tree *t, art_node *n, art_pin **ref, const unsigned char *key, int key_len, int depth) {
    // Search terminated
    if (!n) return NULL;

    // Handle hitting a leaf node
    if (IS_LEAF(n)) {
        art_leaf *l = LEAF_RAW(n);
        if (!leaf_matches(l, key, key_len, depth)) {
            *ref = NULL;
            return l;
        }
        return NULL;
    }

    // Bail if the prefix does not match
    if (n->partial_len) {
        int prefix_len = check_prefix(n, key, key_len, depth);
        if (prefix_len != min(MAX_PREFIX_LEN, n->partial_len)) {
            return NULL;
        }
        depth = depth + n->partial_len;
    }

    // Find child node
    art_pin **child_pin = find_child(n, key[depth]);
    if (!child_pin) return NULL;

    // If the child is leaf, delete from this node
    if (IS_LEAF(*child_pin)) {
        art_leaf *l = LEAF_RAW(PIN_2_NODE(t, *child_pin));
        if (!leaf_matches(l, key, key_len, depth)) {
            remove_child(t, n, ref, key[depth], child_pin);
            return l;
        }
        return NULL;

    // Recurse
    } else {
        return recursive_delete(t, PIN_2_NODE(t, *child_pin), child_pin, key, key_len, depth+1);
    }
}

/**
 * Deletes a value from the ART tree
 * @arg t The tree
 * @arg key The key
 * @arg key_len The length of the key
 * @return NULL if the item was not found, otherwise
 * the value pointer is returned.
 */
void* art_delete(art_tree *t, const unsigned char *key, int key_len) {
    assert(!t->ops || !t->ops->read_only);
    art_leaf *l = recursive_delete(t, PIN_2_NODE(t, t->root), &t->root, key, key_len, 0);
    if (l) {
        t->size--;
        void *old = l->value;
        t->ops->free(t->ops_closure, t, l);
        return old;
    }
    return NULL;
}

// Recursively iterates over the tree
static int recursive_iter(const art_tree *t, art_node *n, art_callback cb, void *data) {
    // Handle base cases
    if (!n) return 0;
    if (IS_LEAF(n)) {
        art_leaf *l = LEAF_RAW(n);
        if(t->ops->deserialize) {
          void *value = t->ops->deserialize(t->ops_closure, t, PIN_2_PTR(t, l->value));
          int rc = cb(data, (const unsigned char*)l->key, l->key_len, value);
          art_release(t, value);
          return rc;
        }
        return cb(data, (const unsigned char*)l->key, l->key_len, l->value);
    }

    int idx, res;
    switch (n->type) {
        case NODE4:
            for (int i=0; i < n->num_children; i++) {
                res = recursive_iter(t, PIN_2_NODE(t, ((art_node4*)n)->children[i]), cb, data);
                if (res) return res;
            }
            break;

        case NODE16:
            for (int i=0; i < n->num_children; i++) {
                res = recursive_iter(t, PIN_2_NODE(t, ((art_node16*)n)->children[i]), cb, data);
                if (res) return res;
            }
            break;

        case NODE48:
            for (int i=0; i < 256; i++) {
                idx = ((art_node48*)n)->keys[i];
                if (!idx) continue;

                res = recursive_iter(t, PIN_2_NODE(t, ((art_node48*)n)->children[idx-1]), cb, data);
                if (res) return res;
            }
            break;

        case NODE256:
            for (int i=0; i < 256; i++) {
                if (!((art_node256*)n)->children[i]) continue;
                res = recursive_iter(t, PIN_2_NODE(t, ((art_node256*)n)->children[i]), cb, data);
                if (res) return res;
            }
            break;

        default:
            abort();
    }
    return 0;
}

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
int art_iter(art_tree *t, art_callback cb, void *data) {
    return recursive_iter(t, PIN_2_NODE(t, t->root), cb, data);
}

/**
 * Checks if a leaf prefix matches
 * @return 0 on success.
 */
static int leaf_prefix_matches(const art_leaf *n, const unsigned char *prefix, int prefix_len) {
    // Fail if the key length is too short
    if (n->key_len < (uint32_t)prefix_len) return 1;

    // Compare the keys
    return memcmp(n->key, prefix, prefix_len);
}

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
int art_iter_prefix(art_tree *t, const unsigned char *key, int key_len, art_callback cb, void *data) {
    art_pin **child_pin;
    art_node *n = PIN_2_NODE(t, t->root);
    int prefix_len, depth = 0;
    while (n) {
        // Might be a leaf
        if (IS_LEAF(n)) {
            n = (art_node*)LEAF_RAW(n);
            // Check if the expanded path matches
            if (!leaf_prefix_matches((art_leaf*)n, key, key_len)) {
                art_leaf *l = (art_leaf*)n;
                if(t->ops->deserialize) {
                    void *value = t->ops->deserialize(t->ops_closure, t, PIN_2_PTR(t, l->value));
                    int rc = cb(data, (const unsigned char*)l->key, l->key_len, value);
                    art_release(t, value);
                    return rc;
                }
                return cb(data, (const unsigned char*)l->key, l->key_len, l->value);
            }
            return 0;
        }

        // If the depth matches the prefix, we need to handle this node
        if (depth == key_len) {
            art_leaf *l = minimum(t, n);
            if (!leaf_prefix_matches(l, key, key_len))
               return recursive_iter(t, n, cb, data);
            return 0;
        }

        // Bail if the prefix does not match
        if (n->partial_len) {
            prefix_len = prefix_mismatch(t, n, key, key_len, depth);

            // Guard if the mis-match is longer than the MAX_PREFIX_LEN
            if ((uint32_t)prefix_len > n->partial_len) {
                prefix_len = n->partial_len;
            }

            // If there is no match, search is terminated
            if (!prefix_len) {
                return 0;

            // If we've matched the prefix, iterate on this node
            } else if (depth + prefix_len == key_len) {
                return recursive_iter(t, n, cb, data);
            }

            // if there is a full match, go deeper
            depth = depth + n->partial_len;
        }

        // Recursively search
        child_pin = find_child(n, key[depth]);
        n = (child_pin) ? PIN_2_NODE(t, *child_pin) : NULL;
        depth++;
    }
    return 0;
}

static uintptr_t write_to_pic(file_serializer_t *ser, const void *vbuff, size_t len) {
  const unsigned char *buff = (unsigned char *)vbuff;
  static unsigned char pad[WRITEALIGN] = { 0 };
  size_t pad_len = len % WRITEALIGN ? (WRITEALIGN - ( len % WRITEALIGN )) : 0;
  struct iovec alignedout[2] = {
    { .iov_base = (void *)buff, .iov_len = len },
    { .iov_base = pad, .iov_len = pad_len }
  };
  ssize_t written;
  while(-1 == (written = pwritev(ser->fd, alignedout, pad_len ? 2 : 1, ser->offset)) &&
        errno == EINTR);
  if(written != (len + pad_len)) return 0;
  size_t offset = ser->offset;
  ser->offset += written;
  return offset;
}
static bool serialize_tree_as_pic(const art_tree *t, art_node *n, art_tree *dt, art_pin **ref, file_serializer_t *ser) {
   // Break if null
    if (!n) {
      *ref = NULL;
      return true;
    }

    // Special case leafs
    if (IS_LEAF(n)) {
        art_leaf *leaf = LEAF_RAW(n);
        uintptr_t offset;
        uintptr_t value = (uintptr_t)leaf->value;
        if(dt->ops->serialize) {
          ssize_t soff = dt->ops->serialize(dt->ops_closure, dt, leaf->value, write_to_pic, ser);
          if(soff < 0) return false;
          value = soff;
        }
        /* This is the value of the leaf */
        offset = write_to_pic(ser, (unsigned char *)&value, sizeof(value));
        if(offset == 0) return false;
        *ref = (art_pin *)SET_LEAF(offset);
        if(write_to_pic(ser, (unsigned char *)&leaf->key_len, sizeof(leaf->key_len) + leaf->key_len) == 0)
            return false;
        return true;
    }

    // Handle each node type
    int i, idx;
    union {
        art_node4 *p1;
        art_node16 *p2;
        art_node48 *p3;
        art_node256 *p4;
    } p;
    union {
        art_node4 n1;
        art_node16 n2;
        art_node48 n3;
        art_node256 n4;
    } towrite;
    memset(&towrite, 0, sizeof(towrite));
    copy_header(&towrite.n1.n, n);
    towrite.n1.n.type = n->type;

    size_t towrite_len = 0;
    switch (n->type) {
        case NODE4:
            towrite_len = sizeof(towrite.n1);
            p.p1 = (art_node4*)n;
            memcpy(towrite.n1.keys, p.p1->keys, sizeof(p.p1->keys));
            for (i=0;i<n->num_children;i++) {
                if(!serialize_tree_as_pic(t, PIN_2_NODE(t, p.p1->children[i]), dt, &towrite.n1.children[i], ser))
                    return false;
            }
            break;

        case NODE16:
            towrite_len = sizeof(towrite.n2);
            p.p2 = (art_node16*)n;
            memcpy(towrite.n2.keys, p.p2->keys, sizeof(p.p2->keys));
            for (i=0;i<n->num_children;i++) {
                if(!serialize_tree_as_pic(t, PIN_2_NODE(t, p.p2->children[i]), dt, &towrite.n2.children[i], ser))
                    return false;
            }
            break;

        case NODE48:
            towrite_len = sizeof(towrite.n3);
            p.p3 = (art_node48*)n;
            memcpy(towrite.n3.keys, p.p3->keys, sizeof(p.p3->keys));
            for (i=0;i<256;i++) {
                idx = ((art_node48*)n)->keys[i]; 
                if (!idx) continue; 
                if(!serialize_tree_as_pic(t, PIN_2_NODE(t, p.p3->children[idx-1]), dt, &towrite.n3.children[idx-1], ser))
                    return false;
            }
            break;

        case NODE256:
            towrite_len = sizeof(towrite.n4);
            p.p4 = (art_node256*)n;
            for (i=0;i<256;i++) {
                if (p.p4->children[i])
                    if(!serialize_tree_as_pic(t, PIN_2_NODE(t, p.p4->children[i]), dt, &towrite.n4.children[i], ser))
                        return false;
            }
            break;

        default:
            abort();
    }
    uintptr_t offset = write_to_pic(ser, (unsigned char *)&towrite, towrite_len);
    if(offset == 0) return false;
    *ref = (art_pin *)offset;
    return true;
}

void art_serializer_destroy(file_serializer_t *ser) {
  if(ser->mapped) {
    munmap((void *)ser->base, ser->offset);
  }
  if(ser->fd >= 0) close(ser->fd);
  free(ser);
}
const void *art_serializer_offset_to_address(file_serializer_t *ser, uintptr_t offset) {
  if(!ser->mapped) return NULL;
  if(ser->base + offset < ser->base) return NULL;
  return (void *)(ser->base + offset);
}
bool art_serializer_finalize(file_serializer_t *ser, uint16_t flags) {
  int rv;
  if(fdatasync(ser->fd) != 0) return false;
  while((rv = pwrite(ser->fd, &flags, sizeof(flags), ART_SER_FLAGS_OFFSET)) == -1 && errno == EINTR);
  if(rv != sizeof(flags)) return false;
  (void)fdatasync(ser->fd);
  return true;
}
file_serializer_t *art_serializer_new(const char *filename, uint16_t version, bool create) {
    errno = 0;
    int fd = open(filename, create ? O_CREAT|O_EXCL|O_RDWR : O_RDONLY, 0640);
    if(fd < 0) return NULL;
    file_serializer_t *ser = calloc(1, sizeof(*ser));
    if(create) {
      struct art_ser_hdr hdr;
      memcpy(&hdr, &ART_SER_HDR, sizeof(hdr));
      hdr.version = version;
      if(write(fd, (void *)&hdr, sizeof(hdr)) == sizeof(hdr)) {
        ser->fd = fd;
        ser->offset = sizeof(hdr);
        return ser;
      }
    }
    else {
      struct art_ser_hdr hdr;
      if(read(fd, &hdr, sizeof(hdr)) == sizeof(hdr)) {
        if(memcmp(&hdr.hdr_ver, &ART_SER_HDR.hdr_ver, sizeof(hdr.hdr_ver)) == 0 &&
           hdr.version == version &&
           hdr.flags & ART_SER_COMPLETE) {
          struct stat sb;
          int rv;
          while((rv = fstat(fd, &sb)) == -1 && errno == EINTR);
          if(rv == 0) {
            ser->fd = fd;
            ser->offset = sb.st_size;
            ser->base = (uintptr_t)mmap(0, ser->offset, PROT_READ, MAP_PRIVATE, fd, 0);
            if(ser->base != (uintptr_t)MAP_FAILED) {
              ser->mapped = true;
              return ser;
            }
          }
        } else {
          errno = EINVAL;
        }
      }
    }
    free(ser);
    close(fd);
    return NULL;
}

bool art_serializer_write_tree(file_serializer_t *ser, const art_tree *t,
                               art_tree_interposition_t *ops, void *closure, size_t *offset) {
    art_tree dt;
    art_tree_init(&dt);
    art_tree_interpose(&dt, 0, ops, closure);
    if(serialize_tree_as_pic(t, PIN_2_NODE(t, t->root), &dt, &dt.root, ser)) {
        *offset = (uintptr_t)dt.root;
        return true;
    }
    return false;
}

bool art_serializer_tree_at_offset(file_serializer_t *ser, art_tree *dt, size_t offset,
                                   art_tree_interposition_t *ops, void *closure) {
    art_tree_init(dt);
    art_tree_interpose(dt, ser, ops, closure);
    if(offset >= dt->ser->offset) return false;
    dt->root = (art_pin *)offset;
    return true;
}

uintptr_t art_serializer_write_custom(file_serializer_t *ser, const void *b, size_t l) {
  return write_to_pic(ser, b, l);
}
