// RUN: ./Tools/vcc -O --emit-mlir %s -o - | filecheck %s
// RUN: ./Tools/vcc -c %s -o %t.o
// RUN: test -s %t.o
// RUN: ./Tools/vcc -S %s -o %t.s
// RUN: test -s %t.s
/*
    An implementation of the ChaCha20 stream cipher (RFC 8439, see bellow).
    Some refrences:
    - Algorithm: https://cr.yp.to/chacha.htmlhttps://cr.yp.to/chacha/chacha-20080120.pdf
    - RFC 8439: https://datatracker.ietf.org/doc/html/rfc8439

    The structure (state matrix, quarter-round, double-round etc.) follows the public RFC, analog to
    the reference Python implementation at https://github.com/ph4r05/py-chacha20poly1305 (chacha.py).

    We have three layers, each calling the previous one:
      - quarter_round: the basic mixing step on four state words
      - chacha20_block: 20 rounds over the 16-word state, producing 64 keystream bytes
      - chacha20_xor:  encryption of (an arbitrary-length) message.

    The main function runs the full encryption on the RFC 8439 section 2.4.2 inputs
    and returns (currently only) the first four ciphertext bytes. 

*/

#include <stddef.h>
#include <stdint.h>


__attribute__((always_inline)) static uint32_t rotl32(uint32_t x, int n) {
    return (x << n) | (x >> (32 - n));
}

__attribute__((always_inline)) static uint32_t load32le(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

__attribute__((always_inline)) static void store32le(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)v;
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
}

// one ChaCha20 quarter-round on the four state words x[a], x[b], x[c], x[d] (shuffles matrix state)
__attribute__((always_inline)) static void quarter_round(uint32_t x[16], int a, int b, int c, int d) {
    x[a]+= x[b]; x[d]^= x[a]; x[d] = rotl32(x[d],16);
    x[c]+= x[d]; x[b]^= x[c]; x[b] = rotl32(x[b],12);
    x[a]+= x[b]; x[d]^= x[a]; x[d] = rotl32(x[d],8);
    x[c]+= x[d]; x[b]^= x[c]; x[b] = rotl32(x[b],7);
}

// produces one 64-byte ChaCha20 keystream block into out
__attribute__((always_inline)) static void chacha20_block(const uint8_t key[32], uint32_t counter, const uint8_t nonce[12], uint8_t out[64]) {
    uint32_t state[16];
    state[0] = 0x61707865; // these constants are the ASCII codes of "expand 32-byte k" and fixed in the algo.
    state[1] = 0x3320646e;
    state[2] = 0x79622d32;
    state[3] = 0x6b206574;
    for (int i = 0; i < 8; i++)
        state[4+i] = load32le(key + 4*i);
    state[12] = counter;
    for (int i = 0; i < 3; i++)
        state[13+i] = load32le(nonce + 4*i);

    uint32_t x[16];
    for (int i = 0; i < 16; i++)
        x[i] = state[i];

    // 20 rounds (10 double rounds each 4 col. rounds then four diag.rounds)
    for (int i = 0; i < 10; i++) {
        quarter_round(x,0,4,8,12);
        quarter_round(x,1,5,9,13);
        quarter_round(x,2,6,10,14);
        quarter_round(x,3,7,11,15);
        quarter_round(x,0,5,10,15);
        quarter_round(x,1,6,11,12);
        quarter_round(x,2,7,8,13);
        quarter_round(x,3,4,9,14);
    }

    for (int i = 0; i < 16; i++)
        store32le(out + 4*i, x[i]+ state[i]);
}

// Encrypt/decrypt len bytes starting from block counter
__attribute__((always_inline)) static inline void chacha20_xor(const uint8_t key[32], const uint8_t nonce[12], uint32_t counter, const uint8_t *in, uint8_t *out, size_t len) {
    uint8_t block[64];
    size_t done = 0;
    while (done < len) {
        chacha20_block(key, counter, nonce, block);
        counter++;
        size_t chunk = len - done;
        if (chunk > 64)
            chunk = 64;
        for (size_t i = 0; i < chunk; i++)
            out[done+i] = in[done+i] ^ block[i];
        done += chunk;
    }
}

__attribute__((always_inline)) int chacha20() {
    uint8_t key[32];
    for (int i = 0; i < 32; i++)
        key[i] = (uint8_t)i;

    // Built with stores (prev had array/string but currently try to avoid llvm.mlir.global since not yet supported )
    // Via stores we can currently run it and test + interpret it.
    uint8_t nonce[12];
    for (int i = 0; i < 12; i++)
        nonce[i] = 0;
    nonce[7] = 0x4a;

    // We test only the first four plaintext bytes ("Ladi") from the RFC input
    uint8_t plaintext[114];
    for (int i = 0; i < 114; i++)
        plaintext[i] = 0;
    plaintext[0] = 0x4c; // L
    plaintext[1] = 0x61; // a
    plaintext[2] = 0x64; // d
    plaintext[3] = 0x69; // i

    uint8_t ciphertext[114];
    chacha20_xor(key, nonce, 1, plaintext, ciphertext, 114);

    // First four ciphertext bytes, equals the RFC 8439 section 2.4.2 value 0x6e2e359a.
    return ((int)ciphertext[0] << 24) | ((int)ciphertext[1] << 16) | ((int)ciphertext[2] << 8) | (int)ciphertext[3];
}

// CHECK:      "builtin.module"() ({
// CHECK:        "llvm.func"() <{{{.*}}"sym_name" = "chacha20"{{.*}}}> ({
// CHECK-NEXT:       ^[[bb7:.*]]():
// CHECK-NEXT:         %[[v8:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v9:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         %[[v10:.*]] = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
// CHECK-NEXT:         %[[v11:.*]] = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK-NEXT:         %[[v12:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:         %[[v13:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i64}> : () -> i64
// CHECK-NEXT:         %[[v14:.*]] = "llvm.mlir.constant"() <{"value" = 74 : i8}> : () -> i8
// CHECK-NEXT:         %[[v15:.*]] = "llvm.mlir.constant"() <{"value" = 114 : i32}> : () -> i32
// CHECK-NEXT:         %[[v16:.*]] = "llvm.mlir.constant"() <{"value" = 76 : i8}> : () -> i8
// CHECK-NEXT:         %[[v17:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[v18:.*]] = "llvm.mlir.constant"() <{"value" = 97 : i8}> : () -> i8
// CHECK-NEXT:         %[[v19:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:         %[[v20:.*]] = "llvm.mlir.constant"() <{"value" = 100 : i8}> : () -> i8
// CHECK-NEXT:         %[[v21:.*]] = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK-NEXT:         %[[v22:.*]] = "llvm.mlir.constant"() <{"value" = 105 : i8}> : () -> i8
// CHECK-NEXT:         %[[v23:.*]] = "llvm.mlir.constant"() <{"value" = 114 : i64}> : () -> i64
// CHECK-NEXT:         %[[v24:.*]] = "llvm.mlir.constant"() <{"value" = 24 : i32}> : () -> i32
// CHECK-NEXT:         %[[v25:.*]] = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
// CHECK-NEXT:         %[[v26:.*]] = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
// CHECK-NEXT:         %[[v27:.*]] = "llvm.mlir.constant"() <{"value" = 1634760805 : i32}> : () -> i32
// CHECK-NEXT:         %[[v28:.*]] = "llvm.mlir.constant"() <{"value" = 857760878 : i32}> : () -> i32
// CHECK-NEXT:         %[[v29:.*]] = "llvm.mlir.constant"() <{"value" = 2036477234 : i32}> : () -> i32
// CHECK-NEXT:         %[[v30:.*]] = "llvm.mlir.constant"() <{"value" = 1797285236 : i32}> : () -> i32
// CHECK-NEXT:         %[[v31:.*]] = "llvm.mlir.constant"() <{"value" = 12 : i64}> : () -> i64
// CHECK-NEXT:         %[[v32:.*]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:         %[[v33:.*]] = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
// CHECK-NEXT:         %[[v34:.*]] = "llvm.mlir.constant"() <{"value" = 64 : i64}> : () -> i64
// CHECK-NEXT:         %[[v35:.*]] = "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
// CHECK-NEXT:         %[[v36:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:         %[[v37:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK-NEXT:         %[[v38:.*]] = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:         %[[v39:.*]] = "llvm.mlir.constant"() <{"value" = 9 : i32}> : () -> i32
// CHECK-NEXT:         %[[v40:.*]] = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
// CHECK-NEXT:         %[[v41:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// CHECK-NEXT:         %[[v42:.*]] = "llvm.mlir.constant"() <{"value" = 14 : i32}> : () -> i32
// CHECK-NEXT:         %[[v43:.*]] = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
// CHECK-NEXT:         %[[v44:.*]] = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
// CHECK-NEXT:         %[[v45:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}> : () -> i8
// CHECK-NEXT:         %[[v46:.*]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 4 : i64, "elem_type" = !llvm.array<16 x i32>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v47:.*]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 4 : i64, "elem_type" = !llvm.array<16 x i32>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v48:.*]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<64 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v49:.*]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v50:.*]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<12 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v51:.*]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<114 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v52:.*]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<114 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb53:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb53]](%[[varg53_0:.*]] : i32):
// CHECK-NEXT:         %[[v55:.*]] = "llvm.icmp"(%[[varg53_0]], %[[v10]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v55]]) [^[[bb56:.*]], ^[[bb57:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb56]]():
// CHECK-NEXT:         %[[v59:.*]] = "llvm.trunc"(%[[varg53_0]]) : (i32) -> i8
// CHECK-NEXT:         %[[v60:.*]] = "llvm.sext"(%[[varg53_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v61:.*]] = "llvm.getelementptr"(%[[v49]], %[[v12]], %[[v60]]) <{"elem_type" = !llvm.array<32 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v59]], %[[v61]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb63:.*]]] : () -> ()
// CHECK-NEXT:       ^[[bb63]]():
// CHECK-NEXT:         %[[v65:.*]] = "llvm.add"(%[[varg53_0]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v65]]) [^[[bb53]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb57]]():
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb67:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb67]](%[[varg67_0:.*]] : i32):
// CHECK-NEXT:         %[[v69:.*]] = "llvm.icmp"(%[[varg67_0]], %[[v11]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v69]]) [^[[bb70:.*]], ^[[bb71:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb70]]():
// CHECK-NEXT:         %[[v73:.*]] = "llvm.sext"(%[[varg67_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v74:.*]] = "llvm.getelementptr"(%[[v50]], %[[v12]], %[[v73]]) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v45]], %[[v74]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb76:.*]]] : () -> ()
// CHECK-NEXT:       ^[[bb76]]():
// CHECK-NEXT:         %[[v78:.*]] = "llvm.add"(%[[varg67_0]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v78]]) [^[[bb67]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb71]]():
// CHECK-NEXT:         %[[v80:.*]] = "llvm.getelementptr"(%[[v50]], %[[v12]], %[[v13]]) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v14]], %[[v80]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb82:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb82]](%[[varg82_0:.*]] : i32):
// CHECK-NEXT:         %[[v84:.*]] = "llvm.icmp"(%[[varg82_0]], %[[v15]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v84]]) [^[[bb85:.*]], ^[[bb86:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb85]]():
// CHECK-NEXT:         %[[v88:.*]] = "llvm.sext"(%[[varg82_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v89:.*]] = "llvm.getelementptr"(%[[v51]], %[[v12]], %[[v88]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v45]], %[[v89]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb91:.*]]] : () -> ()
// CHECK-NEXT:       ^[[bb91]]():
// CHECK-NEXT:         %[[v93:.*]] = "llvm.add"(%[[varg82_0]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v93]]) [^[[bb82]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb86]]():
// CHECK-NEXT:         %[[v95:.*]] = "llvm.getelementptr"(%[[v51]], %[[v12]], %[[v12]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v16]], %[[v95]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v97:.*]] = "llvm.getelementptr"(%[[v51]], %[[v12]], %[[v17]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v18]], %[[v97]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v99:.*]] = "llvm.getelementptr"(%[[v51]], %[[v12]], %[[v19]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v20]], %[[v99]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v101:.*]] = "llvm.getelementptr"(%[[v51]], %[[v12]], %[[v21]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v22]], %[[v101]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v103:.*]] = "llvm.getelementptr"(%[[v49]], %[[v12]], %[[v12]]) <{"elem_type" = !llvm.array<32 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v104:.*]] = "llvm.getelementptr"(%[[v50]], %[[v12]], %[[v12]]) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v105:.*]] = "llvm.getelementptr"(%[[v51]], %[[v12]], %[[v12]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v106:.*]] = "llvm.getelementptr"(%[[v52]], %[[v12]], %[[v12]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.br"(%[[v8]], %[[v12]]) [^[[bb107:.*]]] : (i32, i64) -> ()
// CHECK-NEXT:       ^[[bb107]](%[[varg107_0:.*]] : i32, %[[varg107_1:.*]] : i64):
// CHECK-NEXT:         %[[v109:.*]] = "llvm.icmp"(%[[varg107_1]], %[[v23]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v109]]) [^[[bb110:.*]], ^[[bb111:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb110]]():
// CHECK-NEXT:         "llvm.store"(%[[v27]], %[[v46]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v114:.*]] = "llvm.getelementptr"(%[[v46]], %[[v12]], %[[v17]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v28]], %[[v114]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v116:.*]] = "llvm.getelementptr"(%[[v46]], %[[v12]], %[[v19]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v29]], %[[v116]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v118:.*]] = "llvm.getelementptr"(%[[v46]], %[[v12]], %[[v21]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v30]], %[[v118]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb120:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb120]](%[[varg120_0:.*]] : i32):
// CHECK-NEXT:         %[[v122:.*]] = "llvm.icmp"(%[[varg120_0]], %[[v26]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v122]]) [^[[bb123:.*]], ^[[bb124:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb123]]():
// CHECK-NEXT:         %[[v126:.*]] = "llvm.mul"(%[[v35]], %[[varg120_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v127:.*]] = "llvm.sext"(%[[v126]]) : (i32) -> i64
// CHECK-NEXT:         %[[v128:.*]] = "llvm.getelementptr"(%[[v103]], %[[v127]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v129:.*]] = "llvm.load"(%[[v128]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v130:.*]] = "llvm.zext"(%[[v129]]) : (i8) -> i32
// CHECK-NEXT:         %[[v131:.*]] = "llvm.getelementptr"(%[[v128]], %[[v17]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v132:.*]] = "llvm.load"(%[[v131]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v133:.*]] = "llvm.zext"(%[[v132]]) : (i8) -> i32
// CHECK-NEXT:         %[[v134:.*]] = "llvm.shl"(%[[v133]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v135:.*]] = "llvm.or"(%[[v130]], %[[v134]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v136:.*]] = "llvm.getelementptr"(%[[v128]], %[[v19]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v137:.*]] = "llvm.load"(%[[v136]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v138:.*]] = "llvm.zext"(%[[v137]]) : (i8) -> i32
// CHECK-NEXT:         %[[v139:.*]] = "llvm.shl"(%[[v138]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v140:.*]] = "llvm.or"(%[[v135]], %[[v139]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v141:.*]] = "llvm.getelementptr"(%[[v128]], %[[v21]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v142:.*]] = "llvm.load"(%[[v141]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v143:.*]] = "llvm.zext"(%[[v142]]) : (i8) -> i32
// CHECK-NEXT:         %[[v144:.*]] = "llvm.shl"(%[[v143]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v145:.*]] = "llvm.or"(%[[v140]], %[[v144]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v146:.*]] = "llvm.add"(%[[v35]], %[[varg120_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v147:.*]] = "llvm.sext"(%[[v146]]) : (i32) -> i64
// CHECK-NEXT:         %[[v148:.*]] = "llvm.getelementptr"(%[[v46]], %[[v12]], %[[v147]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v145]], %[[v148]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v150:.*]] = "llvm.add"(%[[varg120_0]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v150]]) [^[[bb120]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb124]]():
// CHECK-NEXT:         %[[v152:.*]] = "llvm.getelementptr"(%[[v46]], %[[v12]], %[[v31]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[varg107_0]], %[[v152]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb154:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb154]](%[[varg154_0:.*]] : i32):
// CHECK-NEXT:         %[[v156:.*]] = "llvm.icmp"(%[[varg154_0]], %[[v32]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v156]]) [^[[bb157:.*]], ^[[bb158:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb157]]():
// CHECK-NEXT:         %[[v160:.*]] = "llvm.mul"(%[[v35]], %[[varg154_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v161:.*]] = "llvm.sext"(%[[v160]]) : (i32) -> i64
// CHECK-NEXT:         %[[v162:.*]] = "llvm.getelementptr"(%[[v104]], %[[v161]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v163:.*]] = "llvm.load"(%[[v162]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v164:.*]] = "llvm.zext"(%[[v163]]) : (i8) -> i32
// CHECK-NEXT:         %[[v165:.*]] = "llvm.getelementptr"(%[[v162]], %[[v17]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v166:.*]] = "llvm.load"(%[[v165]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v167:.*]] = "llvm.zext"(%[[v166]]) : (i8) -> i32
// CHECK-NEXT:         %[[v168:.*]] = "llvm.shl"(%[[v167]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v169:.*]] = "llvm.or"(%[[v164]], %[[v168]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v170:.*]] = "llvm.getelementptr"(%[[v162]], %[[v19]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v171:.*]] = "llvm.load"(%[[v170]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v172:.*]] = "llvm.zext"(%[[v171]]) : (i8) -> i32
// CHECK-NEXT:         %[[v173:.*]] = "llvm.shl"(%[[v172]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v174:.*]] = "llvm.or"(%[[v169]], %[[v173]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v175:.*]] = "llvm.getelementptr"(%[[v162]], %[[v21]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v176:.*]] = "llvm.load"(%[[v175]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v177:.*]] = "llvm.zext"(%[[v176]]) : (i8) -> i32
// CHECK-NEXT:         %[[v178:.*]] = "llvm.shl"(%[[v177]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v179:.*]] = "llvm.or"(%[[v174]], %[[v178]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v180:.*]] = "llvm.add"(%[[v38]], %[[varg154_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v181:.*]] = "llvm.sext"(%[[v180]]) : (i32) -> i64
// CHECK-NEXT:         %[[v182:.*]] = "llvm.getelementptr"(%[[v46]], %[[v12]], %[[v181]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v179]], %[[v182]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v184:.*]] = "llvm.add"(%[[varg154_0]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v184]]) [^[[bb154]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb158]]():
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb186:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb186]](%[[varg186_0:.*]] : i32):
// CHECK-NEXT:         %[[v188:.*]] = "llvm.icmp"(%[[varg186_0]], %[[v25]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v188]]) [^[[bb189:.*]], ^[[bb190:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb189]]():
// CHECK-NEXT:         %[[v192:.*]] = "llvm.sext"(%[[varg186_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v193:.*]] = "llvm.getelementptr"(%[[v46]], %[[v12]], %[[v192]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v194:.*]] = "llvm.load"(%[[v193]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v196:.*]] = "llvm.getelementptr"(%[[v47]], %[[v12]], %[[v192]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v194]], %[[v196]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v198:.*]] = "llvm.add"(%[[varg186_0]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v198]]) [^[[bb186]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb190]]():
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb200:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb200]](%[[varg200_0:.*]] : i32):
// CHECK-NEXT:         %[[v202:.*]] = "llvm.icmp"(%[[varg200_0]], %[[v33]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v202]]) [^[[bb203:.*]], ^[[bb204:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb203]]():
// CHECK-NEXT:         %[[v206:.*]] = "llvm.sext"(%[[v35]]) : (i32) -> i64
// CHECK-NEXT:         %[[v207:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v208:.*]] = "llvm.load"(%[[v207]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v209:.*]] = "llvm.sext"(%[[v9]]) : (i32) -> i64
// CHECK-NEXT:         %[[v210:.*]] = "llvm.getelementptr"(%[[v47]], %[[v209]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v211:.*]] = "llvm.load"(%[[v210]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v212:.*]] = "llvm.add"(%[[v211]], %[[v208]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v212]], %[[v210]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v215:.*]] = "llvm.getelementptr"(%[[v47]], %[[v209]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v216:.*]] = "llvm.load"(%[[v215]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v217:.*]] = "llvm.sext"(%[[v11]]) : (i32) -> i64
// CHECK-NEXT:         %[[v218:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v219:.*]] = "llvm.load"(%[[v218]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v220:.*]] = "llvm.xor"(%[[v219]], %[[v216]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v220]], %[[v218]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v223:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v224:.*]] = "llvm.load"(%[[v223]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v225:.*]] = "llvm.shl"(%[[v224]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v226:.*]] = "llvm.sub"(%[[v10]], %[[v25]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v227:.*]] = "llvm.lshr"(%[[v224]], %[[v226]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v228:.*]] = "llvm.or"(%[[v225]], %[[v227]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v230:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v228]], %[[v230]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v233:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v234:.*]] = "llvm.load"(%[[v233]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v235:.*]] = "llvm.sext"(%[[v26]]) : (i32) -> i64
// CHECK-NEXT:         %[[v236:.*]] = "llvm.getelementptr"(%[[v47]], %[[v235]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v237:.*]] = "llvm.load"(%[[v236]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v238:.*]] = "llvm.add"(%[[v237]], %[[v234]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v238]], %[[v236]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v241:.*]] = "llvm.getelementptr"(%[[v47]], %[[v235]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v242:.*]] = "llvm.load"(%[[v241]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v244:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v245:.*]] = "llvm.load"(%[[v244]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v246:.*]] = "llvm.xor"(%[[v245]], %[[v242]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v246]], %[[v244]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v249:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v250:.*]] = "llvm.load"(%[[v249]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v251:.*]] = "llvm.shl"(%[[v250]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v252:.*]] = "llvm.sub"(%[[v10]], %[[v11]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v253:.*]] = "llvm.lshr"(%[[v250]], %[[v252]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v254:.*]] = "llvm.or"(%[[v251]], %[[v253]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v256:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v254]], %[[v256]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v259:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v260:.*]] = "llvm.load"(%[[v259]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v262:.*]] = "llvm.getelementptr"(%[[v47]], %[[v209]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v263:.*]] = "llvm.load"(%[[v262]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v264:.*]] = "llvm.add"(%[[v263]], %[[v260]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v264]], %[[v262]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v267:.*]] = "llvm.getelementptr"(%[[v47]], %[[v209]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v268:.*]] = "llvm.load"(%[[v267]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v270:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v271:.*]] = "llvm.load"(%[[v270]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v272:.*]] = "llvm.xor"(%[[v271]], %[[v268]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v272]], %[[v270]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v275:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v276:.*]] = "llvm.load"(%[[v275]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v277:.*]] = "llvm.shl"(%[[v276]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v278:.*]] = "llvm.sub"(%[[v10]], %[[v26]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v279:.*]] = "llvm.lshr"(%[[v276]], %[[v278]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v280:.*]] = "llvm.or"(%[[v277]], %[[v279]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v282:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v280]], %[[v282]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v285:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v286:.*]] = "llvm.load"(%[[v285]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v288:.*]] = "llvm.getelementptr"(%[[v47]], %[[v235]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v289:.*]] = "llvm.load"(%[[v288]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v290:.*]] = "llvm.add"(%[[v289]], %[[v286]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v290]], %[[v288]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v293:.*]] = "llvm.getelementptr"(%[[v47]], %[[v235]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v294:.*]] = "llvm.load"(%[[v293]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v296:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v297:.*]] = "llvm.load"(%[[v296]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v298:.*]] = "llvm.xor"(%[[v297]], %[[v294]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v298]], %[[v296]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v301:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v302:.*]] = "llvm.load"(%[[v301]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v303:.*]] = "llvm.shl"(%[[v302]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v304:.*]] = "llvm.sub"(%[[v10]], %[[v36]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v305:.*]] = "llvm.lshr"(%[[v302]], %[[v304]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v306:.*]] = "llvm.or"(%[[v303]], %[[v305]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v308:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v306]], %[[v308]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v310:.*]] = "llvm.sext"(%[[v37]]) : (i32) -> i64
// CHECK-NEXT:         %[[v311:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v312:.*]] = "llvm.load"(%[[v311]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v313:.*]] = "llvm.sext"(%[[v8]]) : (i32) -> i64
// CHECK-NEXT:         %[[v314:.*]] = "llvm.getelementptr"(%[[v47]], %[[v313]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v315:.*]] = "llvm.load"(%[[v314]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v316:.*]] = "llvm.add"(%[[v315]], %[[v312]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v316]], %[[v314]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v319:.*]] = "llvm.getelementptr"(%[[v47]], %[[v313]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v320:.*]] = "llvm.load"(%[[v319]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v321:.*]] = "llvm.sext"(%[[v38]]) : (i32) -> i64
// CHECK-NEXT:         %[[v322:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v323:.*]] = "llvm.load"(%[[v322]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v324:.*]] = "llvm.xor"(%[[v323]], %[[v320]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v324]], %[[v322]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v327:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v328:.*]] = "llvm.load"(%[[v327]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v329:.*]] = "llvm.shl"(%[[v328]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v331:.*]] = "llvm.lshr"(%[[v328]], %[[v226]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v332:.*]] = "llvm.or"(%[[v329]], %[[v331]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v334:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v332]], %[[v334]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v337:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v338:.*]] = "llvm.load"(%[[v337]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v339:.*]] = "llvm.sext"(%[[v39]]) : (i32) -> i64
// CHECK-NEXT:         %[[v340:.*]] = "llvm.getelementptr"(%[[v47]], %[[v339]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v341:.*]] = "llvm.load"(%[[v340]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v342:.*]] = "llvm.add"(%[[v341]], %[[v338]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v342]], %[[v340]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v345:.*]] = "llvm.getelementptr"(%[[v47]], %[[v339]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v346:.*]] = "llvm.load"(%[[v345]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v348:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v349:.*]] = "llvm.load"(%[[v348]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v350:.*]] = "llvm.xor"(%[[v349]], %[[v346]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v350]], %[[v348]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v353:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v354:.*]] = "llvm.load"(%[[v353]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v355:.*]] = "llvm.shl"(%[[v354]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v357:.*]] = "llvm.lshr"(%[[v354]], %[[v252]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v358:.*]] = "llvm.or"(%[[v355]], %[[v357]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v360:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v358]], %[[v360]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v363:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v364:.*]] = "llvm.load"(%[[v363]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v366:.*]] = "llvm.getelementptr"(%[[v47]], %[[v313]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v367:.*]] = "llvm.load"(%[[v366]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v368:.*]] = "llvm.add"(%[[v367]], %[[v364]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v368]], %[[v366]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v371:.*]] = "llvm.getelementptr"(%[[v47]], %[[v313]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v372:.*]] = "llvm.load"(%[[v371]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v374:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v375:.*]] = "llvm.load"(%[[v374]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v376:.*]] = "llvm.xor"(%[[v375]], %[[v372]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v376]], %[[v374]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v379:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v380:.*]] = "llvm.load"(%[[v379]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v381:.*]] = "llvm.shl"(%[[v380]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v383:.*]] = "llvm.lshr"(%[[v380]], %[[v278]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v384:.*]] = "llvm.or"(%[[v381]], %[[v383]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v386:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v384]], %[[v386]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v389:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v390:.*]] = "llvm.load"(%[[v389]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v392:.*]] = "llvm.getelementptr"(%[[v47]], %[[v339]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v393:.*]] = "llvm.load"(%[[v392]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v394:.*]] = "llvm.add"(%[[v393]], %[[v390]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v394]], %[[v392]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v397:.*]] = "llvm.getelementptr"(%[[v47]], %[[v339]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v398:.*]] = "llvm.load"(%[[v397]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v400:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v401:.*]] = "llvm.load"(%[[v400]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v402:.*]] = "llvm.xor"(%[[v401]], %[[v398]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v402]], %[[v400]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v405:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v406:.*]] = "llvm.load"(%[[v405]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v407:.*]] = "llvm.shl"(%[[v406]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v409:.*]] = "llvm.lshr"(%[[v406]], %[[v304]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v410:.*]] = "llvm.or"(%[[v407]], %[[v409]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v412:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v410]], %[[v412]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v414:.*]] = "llvm.sext"(%[[v40]]) : (i32) -> i64
// CHECK-NEXT:         %[[v415:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v416:.*]] = "llvm.load"(%[[v415]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v417:.*]] = "llvm.sext"(%[[v41]]) : (i32) -> i64
// CHECK-NEXT:         %[[v418:.*]] = "llvm.getelementptr"(%[[v47]], %[[v417]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v419:.*]] = "llvm.load"(%[[v418]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v420:.*]] = "llvm.add"(%[[v419]], %[[v416]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v420]], %[[v418]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v423:.*]] = "llvm.getelementptr"(%[[v47]], %[[v417]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v424:.*]] = "llvm.load"(%[[v423]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v425:.*]] = "llvm.sext"(%[[v42]]) : (i32) -> i64
// CHECK-NEXT:         %[[v426:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v427:.*]] = "llvm.load"(%[[v426]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v428:.*]] = "llvm.xor"(%[[v427]], %[[v424]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v428]], %[[v426]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v431:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v432:.*]] = "llvm.load"(%[[v431]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v433:.*]] = "llvm.shl"(%[[v432]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v435:.*]] = "llvm.lshr"(%[[v432]], %[[v226]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v436:.*]] = "llvm.or"(%[[v433]], %[[v435]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v438:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v436]], %[[v438]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v441:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v442:.*]] = "llvm.load"(%[[v441]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v443:.*]] = "llvm.sext"(%[[v33]]) : (i32) -> i64
// CHECK-NEXT:         %[[v444:.*]] = "llvm.getelementptr"(%[[v47]], %[[v443]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v445:.*]] = "llvm.load"(%[[v444]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v446:.*]] = "llvm.add"(%[[v445]], %[[v442]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v446]], %[[v444]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v449:.*]] = "llvm.getelementptr"(%[[v47]], %[[v443]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v450:.*]] = "llvm.load"(%[[v449]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v452:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v453:.*]] = "llvm.load"(%[[v452]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v454:.*]] = "llvm.xor"(%[[v453]], %[[v450]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v454]], %[[v452]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v457:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v458:.*]] = "llvm.load"(%[[v457]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v459:.*]] = "llvm.shl"(%[[v458]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v461:.*]] = "llvm.lshr"(%[[v458]], %[[v252]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v462:.*]] = "llvm.or"(%[[v459]], %[[v461]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v464:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v462]], %[[v464]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v467:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v468:.*]] = "llvm.load"(%[[v467]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v470:.*]] = "llvm.getelementptr"(%[[v47]], %[[v417]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v471:.*]] = "llvm.load"(%[[v470]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v472:.*]] = "llvm.add"(%[[v471]], %[[v468]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v472]], %[[v470]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v475:.*]] = "llvm.getelementptr"(%[[v47]], %[[v417]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v476:.*]] = "llvm.load"(%[[v475]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v478:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v479:.*]] = "llvm.load"(%[[v478]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v480:.*]] = "llvm.xor"(%[[v479]], %[[v476]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v480]], %[[v478]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v483:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v484:.*]] = "llvm.load"(%[[v483]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v485:.*]] = "llvm.shl"(%[[v484]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v487:.*]] = "llvm.lshr"(%[[v484]], %[[v278]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v488:.*]] = "llvm.or"(%[[v485]], %[[v487]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v490:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v488]], %[[v490]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v493:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v494:.*]] = "llvm.load"(%[[v493]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v496:.*]] = "llvm.getelementptr"(%[[v47]], %[[v443]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v497:.*]] = "llvm.load"(%[[v496]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v498:.*]] = "llvm.add"(%[[v497]], %[[v494]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v498]], %[[v496]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v501:.*]] = "llvm.getelementptr"(%[[v47]], %[[v443]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v502:.*]] = "llvm.load"(%[[v501]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v504:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v505:.*]] = "llvm.load"(%[[v504]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v506:.*]] = "llvm.xor"(%[[v505]], %[[v502]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v506]], %[[v504]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v509:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v510:.*]] = "llvm.load"(%[[v509]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v511:.*]] = "llvm.shl"(%[[v510]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v513:.*]] = "llvm.lshr"(%[[v510]], %[[v304]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v514:.*]] = "llvm.or"(%[[v511]], %[[v513]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v516:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v514]], %[[v516]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v518:.*]] = "llvm.sext"(%[[v36]]) : (i32) -> i64
// CHECK-NEXT:         %[[v519:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v520:.*]] = "llvm.load"(%[[v519]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v521:.*]] = "llvm.sext"(%[[v32]]) : (i32) -> i64
// CHECK-NEXT:         %[[v522:.*]] = "llvm.getelementptr"(%[[v47]], %[[v521]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v523:.*]] = "llvm.load"(%[[v522]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v524:.*]] = "llvm.add"(%[[v523]], %[[v520]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v524]], %[[v522]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v527:.*]] = "llvm.getelementptr"(%[[v47]], %[[v521]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v528:.*]] = "llvm.load"(%[[v527]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v529:.*]] = "llvm.sext"(%[[v43]]) : (i32) -> i64
// CHECK-NEXT:         %[[v530:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v531:.*]] = "llvm.load"(%[[v530]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v532:.*]] = "llvm.xor"(%[[v531]], %[[v528]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v532]], %[[v530]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v535:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v536:.*]] = "llvm.load"(%[[v535]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v537:.*]] = "llvm.shl"(%[[v536]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v539:.*]] = "llvm.lshr"(%[[v536]], %[[v226]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v540:.*]] = "llvm.or"(%[[v537]], %[[v539]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v542:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v540]], %[[v542]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v545:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v546:.*]] = "llvm.load"(%[[v545]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v547:.*]] = "llvm.sext"(%[[v44]]) : (i32) -> i64
// CHECK-NEXT:         %[[v548:.*]] = "llvm.getelementptr"(%[[v47]], %[[v547]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v549:.*]] = "llvm.load"(%[[v548]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v550:.*]] = "llvm.add"(%[[v549]], %[[v546]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v550]], %[[v548]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v553:.*]] = "llvm.getelementptr"(%[[v47]], %[[v547]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v554:.*]] = "llvm.load"(%[[v553]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v556:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v557:.*]] = "llvm.load"(%[[v556]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v558:.*]] = "llvm.xor"(%[[v557]], %[[v554]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v558]], %[[v556]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v561:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v562:.*]] = "llvm.load"(%[[v561]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v563:.*]] = "llvm.shl"(%[[v562]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v565:.*]] = "llvm.lshr"(%[[v562]], %[[v252]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v566:.*]] = "llvm.or"(%[[v563]], %[[v565]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v568:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v566]], %[[v568]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v571:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v572:.*]] = "llvm.load"(%[[v571]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v574:.*]] = "llvm.getelementptr"(%[[v47]], %[[v521]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v575:.*]] = "llvm.load"(%[[v574]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v576:.*]] = "llvm.add"(%[[v575]], %[[v572]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v576]], %[[v574]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v579:.*]] = "llvm.getelementptr"(%[[v47]], %[[v521]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v580:.*]] = "llvm.load"(%[[v579]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v582:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v583:.*]] = "llvm.load"(%[[v582]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v584:.*]] = "llvm.xor"(%[[v583]], %[[v580]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v584]], %[[v582]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v587:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v588:.*]] = "llvm.load"(%[[v587]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v589:.*]] = "llvm.shl"(%[[v588]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v591:.*]] = "llvm.lshr"(%[[v588]], %[[v278]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v592:.*]] = "llvm.or"(%[[v589]], %[[v591]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v594:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v592]], %[[v594]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v597:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v598:.*]] = "llvm.load"(%[[v597]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v600:.*]] = "llvm.getelementptr"(%[[v47]], %[[v547]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v601:.*]] = "llvm.load"(%[[v600]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v602:.*]] = "llvm.add"(%[[v601]], %[[v598]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v602]], %[[v600]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v605:.*]] = "llvm.getelementptr"(%[[v47]], %[[v547]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v606:.*]] = "llvm.load"(%[[v605]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v608:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v609:.*]] = "llvm.load"(%[[v608]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v610:.*]] = "llvm.xor"(%[[v609]], %[[v606]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v610]], %[[v608]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v613:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v614:.*]] = "llvm.load"(%[[v613]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v615:.*]] = "llvm.shl"(%[[v614]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v617:.*]] = "llvm.lshr"(%[[v614]], %[[v304]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v618:.*]] = "llvm.or"(%[[v615]], %[[v617]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v620:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v618]], %[[v620]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v623:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v624:.*]] = "llvm.load"(%[[v623]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v626:.*]] = "llvm.getelementptr"(%[[v47]], %[[v209]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v627:.*]] = "llvm.load"(%[[v626]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v628:.*]] = "llvm.add"(%[[v627]], %[[v624]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v628]], %[[v626]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v631:.*]] = "llvm.getelementptr"(%[[v47]], %[[v209]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v632:.*]] = "llvm.load"(%[[v631]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v634:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v635:.*]] = "llvm.load"(%[[v634]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v636:.*]] = "llvm.xor"(%[[v635]], %[[v632]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v636]], %[[v634]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v639:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v640:.*]] = "llvm.load"(%[[v639]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v641:.*]] = "llvm.shl"(%[[v640]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v643:.*]] = "llvm.lshr"(%[[v640]], %[[v226]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v644:.*]] = "llvm.or"(%[[v641]], %[[v643]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v646:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v644]], %[[v646]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v649:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v650:.*]] = "llvm.load"(%[[v649]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v652:.*]] = "llvm.getelementptr"(%[[v47]], %[[v443]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v653:.*]] = "llvm.load"(%[[v652]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v654:.*]] = "llvm.add"(%[[v653]], %[[v650]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v654]], %[[v652]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v657:.*]] = "llvm.getelementptr"(%[[v47]], %[[v443]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v658:.*]] = "llvm.load"(%[[v657]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v660:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v661:.*]] = "llvm.load"(%[[v660]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v662:.*]] = "llvm.xor"(%[[v661]], %[[v658]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v662]], %[[v660]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v665:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v666:.*]] = "llvm.load"(%[[v665]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v667:.*]] = "llvm.shl"(%[[v666]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v669:.*]] = "llvm.lshr"(%[[v666]], %[[v252]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v670:.*]] = "llvm.or"(%[[v667]], %[[v669]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v672:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v670]], %[[v672]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v675:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v676:.*]] = "llvm.load"(%[[v675]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v678:.*]] = "llvm.getelementptr"(%[[v47]], %[[v209]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v679:.*]] = "llvm.load"(%[[v678]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v680:.*]] = "llvm.add"(%[[v679]], %[[v676]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v680]], %[[v678]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v683:.*]] = "llvm.getelementptr"(%[[v47]], %[[v209]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v684:.*]] = "llvm.load"(%[[v683]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v686:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v687:.*]] = "llvm.load"(%[[v686]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v688:.*]] = "llvm.xor"(%[[v687]], %[[v684]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v688]], %[[v686]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v691:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v692:.*]] = "llvm.load"(%[[v691]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v693:.*]] = "llvm.shl"(%[[v692]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v695:.*]] = "llvm.lshr"(%[[v692]], %[[v278]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v696:.*]] = "llvm.or"(%[[v693]], %[[v695]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v698:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v696]], %[[v698]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v701:.*]] = "llvm.getelementptr"(%[[v47]], %[[v529]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v702:.*]] = "llvm.load"(%[[v701]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v704:.*]] = "llvm.getelementptr"(%[[v47]], %[[v443]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v705:.*]] = "llvm.load"(%[[v704]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v706:.*]] = "llvm.add"(%[[v705]], %[[v702]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v706]], %[[v704]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v709:.*]] = "llvm.getelementptr"(%[[v47]], %[[v443]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v710:.*]] = "llvm.load"(%[[v709]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v712:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v713:.*]] = "llvm.load"(%[[v712]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v714:.*]] = "llvm.xor"(%[[v713]], %[[v710]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v714]], %[[v712]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v717:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v718:.*]] = "llvm.load"(%[[v717]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v719:.*]] = "llvm.shl"(%[[v718]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v721:.*]] = "llvm.lshr"(%[[v718]], %[[v304]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v722:.*]] = "llvm.or"(%[[v719]], %[[v721]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v724:.*]] = "llvm.getelementptr"(%[[v47]], %[[v310]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v722]], %[[v724]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v727:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v728:.*]] = "llvm.load"(%[[v727]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v730:.*]] = "llvm.getelementptr"(%[[v47]], %[[v313]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v731:.*]] = "llvm.load"(%[[v730]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v732:.*]] = "llvm.add"(%[[v731]], %[[v728]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v732]], %[[v730]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v735:.*]] = "llvm.getelementptr"(%[[v47]], %[[v313]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v736:.*]] = "llvm.load"(%[[v735]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v738:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v739:.*]] = "llvm.load"(%[[v738]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v740:.*]] = "llvm.xor"(%[[v739]], %[[v736]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v740]], %[[v738]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v743:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v744:.*]] = "llvm.load"(%[[v743]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v745:.*]] = "llvm.shl"(%[[v744]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v747:.*]] = "llvm.lshr"(%[[v744]], %[[v226]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v748:.*]] = "llvm.or"(%[[v745]], %[[v747]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v750:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v748]], %[[v750]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v753:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v754:.*]] = "llvm.load"(%[[v753]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v756:.*]] = "llvm.getelementptr"(%[[v47]], %[[v547]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v757:.*]] = "llvm.load"(%[[v756]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v758:.*]] = "llvm.add"(%[[v757]], %[[v754]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v758]], %[[v756]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v761:.*]] = "llvm.getelementptr"(%[[v47]], %[[v547]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v762:.*]] = "llvm.load"(%[[v761]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v764:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v765:.*]] = "llvm.load"(%[[v764]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v766:.*]] = "llvm.xor"(%[[v765]], %[[v762]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v766]], %[[v764]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v769:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v770:.*]] = "llvm.load"(%[[v769]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v771:.*]] = "llvm.shl"(%[[v770]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v773:.*]] = "llvm.lshr"(%[[v770]], %[[v252]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v774:.*]] = "llvm.or"(%[[v771]], %[[v773]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v776:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v774]], %[[v776]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v779:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v780:.*]] = "llvm.load"(%[[v779]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v782:.*]] = "llvm.getelementptr"(%[[v47]], %[[v313]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v783:.*]] = "llvm.load"(%[[v782]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v784:.*]] = "llvm.add"(%[[v783]], %[[v780]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v784]], %[[v782]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v787:.*]] = "llvm.getelementptr"(%[[v47]], %[[v313]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v788:.*]] = "llvm.load"(%[[v787]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v790:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v791:.*]] = "llvm.load"(%[[v790]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v792:.*]] = "llvm.xor"(%[[v791]], %[[v788]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v792]], %[[v790]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v795:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v796:.*]] = "llvm.load"(%[[v795]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v797:.*]] = "llvm.shl"(%[[v796]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v799:.*]] = "llvm.lshr"(%[[v796]], %[[v278]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v800:.*]] = "llvm.or"(%[[v797]], %[[v799]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v802:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v800]], %[[v802]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v805:.*]] = "llvm.getelementptr"(%[[v47]], %[[v217]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v806:.*]] = "llvm.load"(%[[v805]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v808:.*]] = "llvm.getelementptr"(%[[v47]], %[[v547]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v809:.*]] = "llvm.load"(%[[v808]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v810:.*]] = "llvm.add"(%[[v809]], %[[v806]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v810]], %[[v808]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v813:.*]] = "llvm.getelementptr"(%[[v47]], %[[v547]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v814:.*]] = "llvm.load"(%[[v813]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v816:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v817:.*]] = "llvm.load"(%[[v816]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v818:.*]] = "llvm.xor"(%[[v817]], %[[v814]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v818]], %[[v816]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v821:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v822:.*]] = "llvm.load"(%[[v821]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v823:.*]] = "llvm.shl"(%[[v822]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v825:.*]] = "llvm.lshr"(%[[v822]], %[[v304]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v826:.*]] = "llvm.or"(%[[v823]], %[[v825]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v828:.*]] = "llvm.getelementptr"(%[[v47]], %[[v414]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v826]], %[[v828]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v831:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v832:.*]] = "llvm.load"(%[[v831]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v834:.*]] = "llvm.getelementptr"(%[[v47]], %[[v417]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v835:.*]] = "llvm.load"(%[[v834]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v836:.*]] = "llvm.add"(%[[v835]], %[[v832]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v836]], %[[v834]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v839:.*]] = "llvm.getelementptr"(%[[v47]], %[[v417]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v840:.*]] = "llvm.load"(%[[v839]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v842:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v843:.*]] = "llvm.load"(%[[v842]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v844:.*]] = "llvm.xor"(%[[v843]], %[[v840]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v844]], %[[v842]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v847:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v848:.*]] = "llvm.load"(%[[v847]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v849:.*]] = "llvm.shl"(%[[v848]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v851:.*]] = "llvm.lshr"(%[[v848]], %[[v226]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v852:.*]] = "llvm.or"(%[[v849]], %[[v851]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v854:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v852]], %[[v854]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v857:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v858:.*]] = "llvm.load"(%[[v857]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v860:.*]] = "llvm.getelementptr"(%[[v47]], %[[v235]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v861:.*]] = "llvm.load"(%[[v860]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v862:.*]] = "llvm.add"(%[[v861]], %[[v858]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v862]], %[[v860]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v865:.*]] = "llvm.getelementptr"(%[[v47]], %[[v235]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v866:.*]] = "llvm.load"(%[[v865]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v868:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v869:.*]] = "llvm.load"(%[[v868]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v870:.*]] = "llvm.xor"(%[[v869]], %[[v866]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v870]], %[[v868]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v873:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v874:.*]] = "llvm.load"(%[[v873]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v875:.*]] = "llvm.shl"(%[[v874]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v877:.*]] = "llvm.lshr"(%[[v874]], %[[v252]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v878:.*]] = "llvm.or"(%[[v875]], %[[v877]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v880:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v878]], %[[v880]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v883:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v884:.*]] = "llvm.load"(%[[v883]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v886:.*]] = "llvm.getelementptr"(%[[v47]], %[[v417]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v887:.*]] = "llvm.load"(%[[v886]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v888:.*]] = "llvm.add"(%[[v887]], %[[v884]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v888]], %[[v886]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v891:.*]] = "llvm.getelementptr"(%[[v47]], %[[v417]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v892:.*]] = "llvm.load"(%[[v891]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v894:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v895:.*]] = "llvm.load"(%[[v894]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v896:.*]] = "llvm.xor"(%[[v895]], %[[v892]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v896]], %[[v894]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v899:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v900:.*]] = "llvm.load"(%[[v899]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v901:.*]] = "llvm.shl"(%[[v900]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v903:.*]] = "llvm.lshr"(%[[v900]], %[[v278]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v904:.*]] = "llvm.or"(%[[v901]], %[[v903]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v906:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v904]], %[[v906]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v909:.*]] = "llvm.getelementptr"(%[[v47]], %[[v321]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v910:.*]] = "llvm.load"(%[[v909]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v912:.*]] = "llvm.getelementptr"(%[[v47]], %[[v235]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v913:.*]] = "llvm.load"(%[[v912]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v914:.*]] = "llvm.add"(%[[v913]], %[[v910]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v914]], %[[v912]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v917:.*]] = "llvm.getelementptr"(%[[v47]], %[[v235]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v918:.*]] = "llvm.load"(%[[v917]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v920:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v921:.*]] = "llvm.load"(%[[v920]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v922:.*]] = "llvm.xor"(%[[v921]], %[[v918]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v922]], %[[v920]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v925:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v926:.*]] = "llvm.load"(%[[v925]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v927:.*]] = "llvm.shl"(%[[v926]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v929:.*]] = "llvm.lshr"(%[[v926]], %[[v304]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v930:.*]] = "llvm.or"(%[[v927]], %[[v929]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v932:.*]] = "llvm.getelementptr"(%[[v47]], %[[v518]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v930]], %[[v932]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v935:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v936:.*]] = "llvm.load"(%[[v935]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v938:.*]] = "llvm.getelementptr"(%[[v47]], %[[v521]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v939:.*]] = "llvm.load"(%[[v938]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v940:.*]] = "llvm.add"(%[[v939]], %[[v936]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v940]], %[[v938]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v943:.*]] = "llvm.getelementptr"(%[[v47]], %[[v521]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v944:.*]] = "llvm.load"(%[[v943]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v946:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v947:.*]] = "llvm.load"(%[[v946]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v948:.*]] = "llvm.xor"(%[[v947]], %[[v944]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v948]], %[[v946]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v951:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v952:.*]] = "llvm.load"(%[[v951]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v953:.*]] = "llvm.shl"(%[[v952]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v955:.*]] = "llvm.lshr"(%[[v952]], %[[v226]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v956:.*]] = "llvm.or"(%[[v953]], %[[v955]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v958:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v956]], %[[v958]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v961:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v962:.*]] = "llvm.load"(%[[v961]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v964:.*]] = "llvm.getelementptr"(%[[v47]], %[[v339]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v965:.*]] = "llvm.load"(%[[v964]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v966:.*]] = "llvm.add"(%[[v965]], %[[v962]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v966]], %[[v964]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v969:.*]] = "llvm.getelementptr"(%[[v47]], %[[v339]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v970:.*]] = "llvm.load"(%[[v969]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v972:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v973:.*]] = "llvm.load"(%[[v972]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v974:.*]] = "llvm.xor"(%[[v973]], %[[v970]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v974]], %[[v972]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v977:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v978:.*]] = "llvm.load"(%[[v977]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v979:.*]] = "llvm.shl"(%[[v978]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v981:.*]] = "llvm.lshr"(%[[v978]], %[[v252]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v982:.*]] = "llvm.or"(%[[v979]], %[[v981]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v984:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v982]], %[[v984]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v987:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v988:.*]] = "llvm.load"(%[[v987]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v990:.*]] = "llvm.getelementptr"(%[[v47]], %[[v521]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v991:.*]] = "llvm.load"(%[[v990]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v992:.*]] = "llvm.add"(%[[v991]], %[[v988]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v992]], %[[v990]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v995:.*]] = "llvm.getelementptr"(%[[v47]], %[[v521]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v996:.*]] = "llvm.load"(%[[v995]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v998:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v999:.*]] = "llvm.load"(%[[v998]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1000:.*]] = "llvm.xor"(%[[v999]], %[[v996]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v1000]], %[[v998]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1003:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1004:.*]] = "llvm.load"(%[[v1003]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1005:.*]] = "llvm.shl"(%[[v1004]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1007:.*]] = "llvm.lshr"(%[[v1004]], %[[v278]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1008:.*]] = "llvm.or"(%[[v1005]], %[[v1007]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1010:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1008]], %[[v1010]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1013:.*]] = "llvm.getelementptr"(%[[v47]], %[[v425]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1014:.*]] = "llvm.load"(%[[v1013]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1016:.*]] = "llvm.getelementptr"(%[[v47]], %[[v339]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1017:.*]] = "llvm.load"(%[[v1016]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1018:.*]] = "llvm.add"(%[[v1017]], %[[v1014]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v1018]], %[[v1016]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1021:.*]] = "llvm.getelementptr"(%[[v47]], %[[v339]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1022:.*]] = "llvm.load"(%[[v1021]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1024:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1025:.*]] = "llvm.load"(%[[v1024]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1026:.*]] = "llvm.xor"(%[[v1025]], %[[v1022]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v1026]], %[[v1024]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1029:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1030:.*]] = "llvm.load"(%[[v1029]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1031:.*]] = "llvm.shl"(%[[v1030]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1033:.*]] = "llvm.lshr"(%[[v1030]], %[[v304]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1034:.*]] = "llvm.or"(%[[v1031]], %[[v1033]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1036:.*]] = "llvm.getelementptr"(%[[v47]], %[[v206]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1034]], %[[v1036]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1038:.*]] = "llvm.add"(%[[varg200_0]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v1038]]) [^[[bb200]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb204]]():
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb1040:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb1040]](%[[varg1040_0:.*]] : i32):
// CHECK-NEXT:         %[[v1042:.*]] = "llvm.icmp"(%[[varg1040_0]], %[[v25]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v1042]]) [^[[bb1043:.*]], ^[[bb1044:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb1043]]():
// CHECK-NEXT:         %[[v1046:.*]] = "llvm.mul"(%[[v35]], %[[varg1040_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1047:.*]] = "llvm.sext"(%[[v1046]]) : (i32) -> i64
// CHECK-NEXT:         %[[v1048:.*]] = "llvm.getelementptr"(%[[v48]], %[[v1047]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1049:.*]] = "llvm.sext"(%[[varg1040_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v1050:.*]] = "llvm.getelementptr"(%[[v47]], %[[v12]], %[[v1049]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1051:.*]] = "llvm.load"(%[[v1050]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1053:.*]] = "llvm.getelementptr"(%[[v46]], %[[v12]], %[[v1049]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1054:.*]] = "llvm.load"(%[[v1053]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1055:.*]] = "llvm.add"(%[[v1051]], %[[v1054]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1056:.*]] = "llvm.trunc"(%[[v1055]]) : (i32) -> i8
// CHECK-NEXT:         "llvm.store"(%[[v1056]], %[[v1048]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1058:.*]] = "llvm.lshr"(%[[v1055]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1059:.*]] = "llvm.trunc"(%[[v1058]]) : (i32) -> i8
// CHECK-NEXT:         %[[v1060:.*]] = "llvm.getelementptr"(%[[v1048]], %[[v17]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1059]], %[[v1060]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1062:.*]] = "llvm.lshr"(%[[v1055]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1063:.*]] = "llvm.trunc"(%[[v1062]]) : (i32) -> i8
// CHECK-NEXT:         %[[v1064:.*]] = "llvm.getelementptr"(%[[v1048]], %[[v19]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1063]], %[[v1064]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1066:.*]] = "llvm.lshr"(%[[v1055]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1067:.*]] = "llvm.trunc"(%[[v1066]]) : (i32) -> i8
// CHECK-NEXT:         %[[v1068:.*]] = "llvm.getelementptr"(%[[v1048]], %[[v21]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1067]], %[[v1068]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1070:.*]] = "llvm.add"(%[[varg1040_0]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v1070]]) [^[[bb1040]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb1044]]():
// CHECK-NEXT:         %[[v1072:.*]] = "llvm.add"(%[[varg107_0]], %[[v8]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1073:.*]] = "llvm.sub"(%[[v23]], %[[varg107_1]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[v1074:.*]] = "llvm.icmp"(%[[v1073]], %[[v34]]) <{"predicate" = 8 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v1074]], %[[v1073]]) [^[[bb1075:.*]], ^[[bb1076:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
// CHECK-NEXT:       ^[[bb1075]]():
// CHECK-NEXT:         "llvm.br"(%[[v34]]) [^[[bb1076]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb1076]](%[[varg1076_0:.*]] : i64):
// CHECK-NEXT:         "llvm.br"(%[[v12]]) [^[[bb1079:.*]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb1079]](%[[varg1079_0:.*]] : i64):
// CHECK-NEXT:         %[[v1081:.*]] = "llvm.icmp"(%[[varg1079_0]], %[[varg1076_0]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v1081]]) [^[[bb1082:.*]], ^[[bb1083:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb1082]]():
// CHECK-NEXT:         %[[v1085:.*]] = "llvm.add"(%[[varg107_1]], %[[varg1079_0]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[v1086:.*]] = "llvm.getelementptr"(%[[v105]], %[[v1085]]) <{"elem_type" = i8, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1087:.*]] = "llvm.load"(%[[v1086]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1088:.*]] = "llvm.zext"(%[[v1087]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1089:.*]] = "llvm.getelementptr"(%[[v48]], %[[v12]], %[[varg1079_0]]) <{"elem_type" = !llvm.array<64 x i8>, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1090:.*]] = "llvm.load"(%[[v1089]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1091:.*]] = "llvm.zext"(%[[v1090]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1092:.*]] = "llvm.xor"(%[[v1088]], %[[v1091]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1093:.*]] = "llvm.trunc"(%[[v1092]]) : (i32) -> i8
// CHECK-NEXT:         %[[v1095:.*]] = "llvm.getelementptr"(%[[v106]], %[[v1085]]) <{"elem_type" = i8, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1093]], %[[v1095]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1097:.*]] = "llvm.add"(%[[varg1079_0]], %[[v17]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v1097]]) [^[[bb1079]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb1083]]():
// CHECK-NEXT:         %[[v1099:.*]] = "llvm.add"(%[[varg107_1]], %[[varg1076_0]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v1072]], %[[v1099]]) [^[[bb107]]] : (i32, i64) -> ()
// CHECK-NEXT:       ^[[bb111]]():
// CHECK-NEXT:         %[[v1101:.*]] = "llvm.getelementptr"(%[[v52]], %[[v12]], %[[v12]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1102:.*]] = "llvm.load"(%[[v1101]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1103:.*]] = "llvm.zext"(%[[v1102]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1104:.*]] = "llvm.shl"(%[[v1103]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1105:.*]] = "llvm.getelementptr"(%[[v52]], %[[v12]], %[[v17]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1106:.*]] = "llvm.load"(%[[v1105]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1107:.*]] = "llvm.zext"(%[[v1106]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1108:.*]] = "llvm.shl"(%[[v1107]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1109:.*]] = "llvm.or"(%[[v1104]], %[[v1108]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1110:.*]] = "llvm.getelementptr"(%[[v52]], %[[v12]], %[[v19]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1111:.*]] = "llvm.load"(%[[v1110]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1112:.*]] = "llvm.zext"(%[[v1111]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1113:.*]] = "llvm.shl"(%[[v1112]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1114:.*]] = "llvm.or"(%[[v1109]], %[[v1113]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1115:.*]] = "llvm.getelementptr"(%[[v52]], %[[v12]], %[[v21]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1116:.*]] = "llvm.load"(%[[v1115]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1117:.*]] = "llvm.zext"(%[[v1116]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1118:.*]] = "llvm.or"(%[[v1114]], %[[v1117]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.return"(%[[v1118]]) : (i32) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "o", "dlti.legal_int_widths" = array<i32: 32, 64>, "dlti.stack_alignment" = 128 : i64, "dlti.function_pointer_alignment" = #dlti.function_pointer_alignment<32, function_dependent = true>>, "llvm.ident" = "Homebrew clang version 22.1.7", "llvm.module_asm" = [], "llvm.target_triple" = "arm64-apple-macosx26.0.0"} : () -> ()
