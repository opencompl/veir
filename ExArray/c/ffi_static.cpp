#include <cstring>
#include <stdint.h>
#include <lean/lean.h>
#include <lean/lean_gmp.h>
#include <inttypes.h>

typedef size_t usize;
typedef uint8_t uint8;

extern "C" {

__attribute__((always_inline))
lean_object * buffed_zalloc_object(size_t sz) {
    void * r = malloc(sz);
    if (r == nullptr) lean_internal_panic_out_of_memory();
    lean_object * o = (lean_object*)r;
    // not a small object
    o->m_cs_sz = 0;
    return o;
}

__attribute__((always_inline))
static inline lean_obj_res buffed_alloc_ex_array(unsigned elem_size, size_t size, size_t capacity) {
    lean_sarray_object * o = (lean_sarray_object*)buffed_zalloc_object(sizeof(lean_sarray_object) + elem_size*capacity);
    lean_set_st_header((lean_object*)o, LeanScalarArray, elem_size);
    o->m_size = size;
    o->m_capacity = capacity;
    return (lean_object*)o;
}


// IMPLEMENTATION NOTE
// For some reason, it's much faster to copy paste functions defined in `lean.h`
// in this file, even though the source code should be available to lean...
//
// Maybe we should try to compile the lean std lib with LTO enabled??

__attribute__((always_inline))
static inline lean_sarray_object * buffed_to_ex_array(lean_object * o) { return (lean_sarray_object*)(o); }

__attribute__((always_inline))
static inline uint8_t* buffed_ex_array_cptr(lean_object * o) { return buffed_to_ex_array(o)->m_data; }

__attribute__((always_inline))
static inline bool buffed_is_exclusive(lean_object * o) {
    if (LEAN_LIKELY(o->m_rc > 0)) {
        return o->m_rc == 1;
    } else {
        return false;
    }
}

__attribute__((always_inline))
static inline size_t buffed_sarray_capacity(lean_object * o) { return buffed_to_ex_array(o)->m_capacity; }

__attribute__((always_inline))
static inline size_t buffed_sarray_size(b_lean_obj_arg o) { return buffed_to_ex_array(o)->m_size; }

__attribute__((always_inline))
uint64_t buffed_ex_array_usize(b_lean_obj_arg o) { return buffed_to_ex_array(o)->m_size; }

__attribute__((always_inline))
lean_obj_res buffed_ex_array_data(lean_obj_arg a) {
    usize sz            = lean_array_size(a);
    lean_obj_res r      = lean_alloc_array(sz, sz);
    uint8 * it          = buffed_ex_array_cptr(a);
    uint8 * end         = it + sz;
    lean_object ** dest = lean_array_cptr(r);
    for (; it != end; ++it, ++dest) {
        *dest = lean_box(*it);
    }
    lean_dec(a);
    return r;
}

__attribute__((always_inline))
lean_obj_res buffed_ex_array_mk(lean_obj_arg a) {
    usize sz      = lean_array_size(a);
    lean_obj_res r     = buffed_alloc_ex_array(1, sz, sz);
    lean_object ** it  = lean_array_cptr(a);
    lean_object ** end = it + sz;
    uint8 * dest  = buffed_ex_array_cptr(r);
    for (; it != end; ++it, ++dest) {
        *dest = lean_unbox(*it);
    }
    lean_dec(a);
    return r;
}

__attribute__((always_inline))
lean_obj_res buffed_mk_empty_ex_array(b_lean_obj_arg capacity) {
    if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
    return buffed_alloc_ex_array(1, 0, lean_unbox(capacity));
}

__attribute__((always_inline))
lean_obj_res buffed_copy_ex_array(lean_obj_arg a, size_t cap) {
    unsigned esz   = lean_sarray_elem_size(a);
    size_t sz      = buffed_sarray_size(a);
    lean_object * r     = buffed_alloc_ex_array(esz, sz, cap);
    uint8 * it     = buffed_ex_array_cptr(a);
    uint8 * dest   = buffed_ex_array_cptr(r);
    memcpy(dest, it, esz*sz);
    lean_dec(a);
    return r;
}

__attribute__((always_inline))
static inline lean_obj_res buffed_ex_array_ensure_capacity(lean_obj_arg a, size_t min_cap, bool exact) {
    size_t cap = buffed_sarray_capacity(a);
    if (min_cap <= cap) {
        return a;
    } else {
        printf("\n\nIncreasing size, needed %zu but I'm %zu!\n\n", min_cap, cap);
        return buffed_copy_ex_array(a, exact ? min_cap : min_cap * 2);
    }
}

__attribute__((always_inline))
lean_obj_res buffed_ex_array_ensure_exclusive(lean_obj_arg a) {
    if (buffed_is_exclusive(a)) {
        return a;
    } else {
        printf("\n\nNON EXCLUSIVE ARRAY!\n\n");
        return buffed_copy_ex_array(a, buffed_sarray_capacity(a));
    }
}

__attribute__((always_inline))
lean_obj_res buffed_ex_array_extend(lean_obj_arg a, size_t len) {
    size_t sz = buffed_sarray_size(a);
    lean_object * r1 = buffed_ex_array_ensure_capacity(a, sz + len, false);
    lean_object * r = buffed_ex_array_ensure_exclusive(r1);
    uint8 *start = buffed_ex_array_cptr(r);
    memset(start + sz, 0, len);
    buffed_to_ex_array(r)->m_size = sz + len;
    return r;
}

__attribute__((always_inline))
uint8_t buffed_ex_array_uget(b_lean_obj_arg a, size_t i) {
    assert(i < buffed_sarray_size(a));
    return buffed_ex_array_cptr(a)[i];
}

__attribute__((always_inline))
lean_object * buffed_ex_array_uset(lean_obj_arg a, size_t i, uint8_t v) {
    lean_obj_res r;
    if (buffed_is_exclusive(a)) r = a;
    else r = buffed_copy_ex_array(a, buffed_sarray_capacity(a));
    uint8_t * it = buffed_ex_array_cptr(r) + i;
    *it = v;
    return r;
}

__attribute__((always_inline))
lean_obj_res buffed_ex_array_size(b_lean_obj_arg a) {
    return lean_box(buffed_sarray_size(a));
}

__attribute__((always_inline))
lean_obj_res buffed_ex_array_push(lean_obj_arg a, uint8 b) {
    lean_object * r = buffed_ex_array_ensure_exclusive(buffed_ex_array_ensure_capacity(a, buffed_sarray_size(a) + 1, /* exact */ false));
    size_t & sz  = buffed_to_ex_array(r)->m_size;
    uint8 * it   = buffed_ex_array_cptr(r) + sz;
    *it = b;
    sz++;
    return r;
}

__attribute__((always_inline))
uint32_t buffed_ex_array_read32(b_lean_obj_arg a, size_t offset) {
    return *(uint32_t *)(buffed_ex_array_cptr(a) + offset);
}

__attribute__((always_inline))
uint64_t buffed_ex_array_read64(b_lean_obj_arg a, size_t offset) {
    return *(uint64_t *)(buffed_ex_array_cptr(a) + offset);
}

__attribute__((always_inline))
lean_obj_res buffed_ex_array_blit32(lean_obj_arg a, size_t offset, uint32_t x) {
    lean_object * r = buffed_ex_array_ensure_exclusive(a);
    uint32_t * p = (uint32_t *)(buffed_ex_array_cptr(r) + offset);
    *p = x;
    return r;
}

__attribute__((always_inline))
lean_obj_res buffed_ex_array_blit64(lean_obj_arg a, size_t offset, uint64_t x) {
    lean_object * r = buffed_ex_array_ensure_exclusive(a);
    uint64_t * p = (uint64_t *)(buffed_ex_array_cptr(r) + offset);
    *p = x;
    return r;
}

lean_obj_res buffed_ex_array_read(b_lean_obj_arg _w, b_lean_obj_arg buf, uint64_t n, uint64_t len) {
    if (len < 8) { // scalar
      uint64_t res = *(uint64_t *)(buffed_ex_array_cptr(buf) + n);
      res = res & ~((uint64_t)(-1) << (len * 8));
      return lean_box(res);
    } else {
      uint8_t *p = (uint8_t *)(buffed_ex_array_cptr(buf) + n);
      mpz_t res;
      mpz_init(res);
      mpz_import(res, len, -1, sizeof(uint8_t), 0, 0, p);
      return lean_alloc_mpz(res);
    }
}

struct mpz_object {
    lean_object m_header;
    mpz_t       m_value;
};

// [[gnu::noinline]]
lean_obj_res buffed_ex_array_blit(b_lean_obj_arg *w, lean_obj_arg a, size_t offset, uint64_t len, lean_obj_arg o) {
    lean_object *r = buffed_ex_array_ensure_exclusive(a);
    uint8_t *p = (uint8_t *)(buffed_ex_array_cptr(r) + offset);
    if (lean_is_scalar(o)) {
      uint64_t val = lean_unbox(o);
      for (int i = 0; i < len; i++) {
        p[i] = (uint8_t)(val >> 8*i);
      }
    } else {
      mpz_object *nat = (mpz_object *)o;
      mpz_t temp;
      mpz_init(temp);
      for (int i = 0; i < len; i++) {
        mpz_tdiv_q_2exp(temp, nat->m_value, i * 8);
        unsigned long val = mpz_get_ui(temp) & 0xFF;
        p[i] = (uint8_t)val;
      }
      mpz_clear(temp);
    }

    return r;
}

}
