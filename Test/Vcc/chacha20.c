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

    The cipher is built up in three layers, each calling the previous one:
      - quarter_round: the basic mixing step on four state words
      - chacha20_block: 20 rounds over the 16-word state, producing 64 keystream bytes
      - chacha20_xor:   encryption of (an arbitrary-length) message.

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

int main() {
    uint8_t key[32];
    for (int i = 0; i < 32; i++)
        key[i] = (uint8_t)i;

    uint8_t nonce[12] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                         0x00, 0x4a, 0x00, 0x00, 0x00, 0x00};
    
                         const char *msg = "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
    
    uint8_t plaintext[114];
    for (int i = 0; i < 114; i++)
        plaintext[i] = (uint8_t)msg[i];

    uint8_t ciphertext[114];
    chacha20_xor(key, nonce, 1, plaintext, ciphertext, 114);

    // Return the first four ciphertext bytes (so basically the start of the first block) which we will check against the RFC 8439 expected value (0x6e2e359a).
    // Currently "restricted" to return only the first four bytes to obtain a 32bit value.
    return ((int)ciphertext[0] << 24) | ((int)ciphertext[1] << 16) | ((int)ciphertext[2] << 8) | (int)ciphertext[3];
}

// CHECK:      "builtin.module"() ({
// CHECK:        "llvm.func"() <{{{.*}}"sym_name" = "main"{{.*}}}> ({
// CHECK-NEXT:       ^[[bb11:.*]]():
// CHECK-NEXT:         %[[v12:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v13:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         %[[v14:.*]] = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
// CHECK-NEXT:         %[[v15:.*]] = "llvm.mlir.addressof"() <{"global_name" = @__const.main.nonce}> : () -> !llvm.ptr
// CHECK-NEXT:         %[[v16:.*]] = "llvm.mlir.constant"() <{"value" = 12 : i64}> : () -> i64
// CHECK-NEXT:         %[[v17:.*]] = "llvm.mlir.constant"() <{"value" = 114 : i32}> : () -> i32
// CHECK-NEXT:         %[[v18:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:         %[[v19:.*]] = "llvm.mlir.constant"() <{"value" = 114 : i64}> : () -> i64
// CHECK-NEXT:         %[[v20:.*]] = "llvm.mlir.constant"() <{"value" = 24 : i32}> : () -> i32
// CHECK-NEXT:         %[[v21:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[v22:.*]] = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
// CHECK-NEXT:         %[[v23:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:         %[[v24:.*]] = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
// CHECK-NEXT:         %[[v25:.*]] = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK-NEXT:         %[[v26:.*]] = "llvm.mlir.constant"() <{"value" = 1634760805 : i32}> : () -> i32
// CHECK-NEXT:         %[[v27:.*]] = "llvm.mlir.constant"() <{"value" = 857760878 : i32}> : () -> i32
// CHECK-NEXT:         %[[v28:.*]] = "llvm.mlir.constant"() <{"value" = 2036477234 : i32}> : () -> i32
// CHECK-NEXT:         %[[v29:.*]] = "llvm.mlir.constant"() <{"value" = 1797285236 : i32}> : () -> i32
// CHECK-NEXT:         %[[v30:.*]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:         %[[v31:.*]] = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
// CHECK-NEXT:         %[[v32:.*]] = "llvm.mlir.constant"() <{"value" = 64 : i64}> : () -> i64
// CHECK-NEXT:         %[[v33:.*]] = "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
// CHECK-NEXT:         %[[v34:.*]] = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK-NEXT:         %[[v35:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:         %[[v36:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK-NEXT:         %[[v37:.*]] = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:         %[[v38:.*]] = "llvm.mlir.constant"() <{"value" = 9 : i32}> : () -> i32
// CHECK-NEXT:         %[[v39:.*]] = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
// CHECK-NEXT:         %[[v40:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// CHECK-NEXT:         %[[v41:.*]] = "llvm.mlir.constant"() <{"value" = 14 : i32}> : () -> i32
// CHECK-NEXT:         %[[v42:.*]] = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
// CHECK-NEXT:         %[[v43:.*]] = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
// CHECK-NEXT:         %[[v44:.*]] = "llvm.mlir.addressof"() <{"global_name" = @".str"}> : () -> !llvm.ptr
// CHECK-NEXT:         %[[v45:.*]] = "llvm.alloca"(%[[v12]]) <{"alignment" = 4 : i64, "elem_type" = !llvm.array<16 x i32>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v46:.*]] = "llvm.alloca"(%[[v12]]) <{"alignment" = 4 : i64, "elem_type" = !llvm.array<16 x i32>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v47:.*]] = "llvm.alloca"(%[[v12]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<64 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v48:.*]] = "llvm.alloca"(%[[v12]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v49:.*]] = "llvm.alloca"(%[[v12]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<12 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v50:.*]] = "llvm.alloca"(%[[v12]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<114 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v51:.*]] = "llvm.alloca"(%[[v12]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<114 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         "llvm.br"(%[[v13]]) [^[[bb52:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb52]](%[[varg52_0:.*]] : i32):
// CHECK-NEXT:         %[[v54:.*]] = "llvm.icmp"(%[[varg52_0]], %[[v14]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v54]]) [^[[bb55:.*]], ^[[bb56:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb55]]():
// CHECK-NEXT:         %[[v58:.*]] = "llvm.trunc"(%[[varg52_0]]) : (i32) -> i8
// CHECK-NEXT:         %[[v59:.*]] = "llvm.sext"(%[[varg52_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v60:.*]] = "llvm.getelementptr"(%[[v48]], %[[v18]], %[[v59]]) <{"elem_type" = !llvm.array<32 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v58]], %[[v60]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb62:.*]]] : () -> ()
// CHECK-NEXT:       ^[[bb62]]():
// CHECK-NEXT:         %[[v64:.*]] = "llvm.add"(%[[varg52_0]], %[[v12]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v64]]) [^[[bb52]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb56]]():
// CHECK-NEXT:         "llvm.intr.memcpy"(%[[v49]], %[[v15]], %[[v16]]) <{"arg_attrs" = [{"llvm.align" = 1 : i64}, {"llvm.align" = 1 : i64}, {}], "isVolatile" = 0 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v13]]) [^[[bb67:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb67]](%[[varg67_0:.*]] : i32):
// CHECK-NEXT:         %[[v69:.*]] = "llvm.icmp"(%[[varg67_0]], %[[v17]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v69]]) [^[[bb70:.*]], ^[[bb71:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb70]]():
// CHECK-NEXT:         %[[v73:.*]] = "llvm.sext"(%[[varg67_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v74:.*]] = "llvm.getelementptr"(%[[v44]], %[[v73]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v75:.*]] = "llvm.load"(%[[v74]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v77:.*]] = "llvm.getelementptr"(%[[v50]], %[[v18]], %[[v73]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v75]], %[[v77]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb79:.*]]] : () -> ()
// CHECK-NEXT:       ^[[bb79]]():
// CHECK-NEXT:         %[[v81:.*]] = "llvm.add"(%[[varg67_0]], %[[v12]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v81]]) [^[[bb67]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb71]]():
// CHECK-NEXT:         %[[v83:.*]] = "llvm.getelementptr"(%[[v48]], %[[v18]], %[[v18]]) <{"elem_type" = !llvm.array<32 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v84:.*]] = "llvm.getelementptr"(%[[v49]], %[[v18]], %[[v18]]) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v85:.*]] = "llvm.getelementptr"(%[[v50]], %[[v18]], %[[v18]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v86:.*]] = "llvm.getelementptr"(%[[v51]], %[[v18]], %[[v18]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.br"(%[[v12]], %[[v18]]) [^[[bb87:.*]]] : (i32, i64) -> ()
// CHECK-NEXT:       ^[[bb87]](%[[varg87_0:.*]] : i32, %[[varg87_1:.*]] : i64):
// CHECK-NEXT:         %[[v89:.*]] = "llvm.icmp"(%[[varg87_1]], %[[v19]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v89]]) [^[[bb90:.*]], ^[[bb91:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb90]]():
// CHECK-NEXT:         "llvm.store"(%[[v26]], %[[v45]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v94:.*]] = "llvm.getelementptr"(%[[v45]], %[[v18]], %[[v21]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v27]], %[[v94]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v96:.*]] = "llvm.getelementptr"(%[[v45]], %[[v18]], %[[v23]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v28]], %[[v96]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v98:.*]] = "llvm.getelementptr"(%[[v45]], %[[v18]], %[[v25]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v29]], %[[v98]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v13]]) [^[[bb100:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb100]](%[[varg100_0:.*]] : i32):
// CHECK-NEXT:         %[[v102:.*]] = "llvm.icmp"(%[[varg100_0]], %[[v24]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v102]]) [^[[bb103:.*]], ^[[bb104:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb103]]():
// CHECK-NEXT:         %[[v106:.*]] = "llvm.mul"(%[[v33]], %[[varg100_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v107:.*]] = "llvm.sext"(%[[v106]]) : (i32) -> i64
// CHECK-NEXT:         %[[v108:.*]] = "llvm.getelementptr"(%[[v83]], %[[v107]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v109:.*]] = "llvm.load"(%[[v108]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v110:.*]] = "llvm.zext"(%[[v109]]) : (i8) -> i32
// CHECK-NEXT:         %[[v111:.*]] = "llvm.getelementptr"(%[[v108]], %[[v21]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v112:.*]] = "llvm.load"(%[[v111]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v113:.*]] = "llvm.zext"(%[[v112]]) : (i8) -> i32
// CHECK-NEXT:         %[[v114:.*]] = "llvm.shl"(%[[v113]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v115:.*]] = "llvm.or"(%[[v110]], %[[v114]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v116:.*]] = "llvm.getelementptr"(%[[v108]], %[[v23]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v117:.*]] = "llvm.load"(%[[v116]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v118:.*]] = "llvm.zext"(%[[v117]]) : (i8) -> i32
// CHECK-NEXT:         %[[v119:.*]] = "llvm.shl"(%[[v118]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v120:.*]] = "llvm.or"(%[[v115]], %[[v119]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v121:.*]] = "llvm.getelementptr"(%[[v108]], %[[v25]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v122:.*]] = "llvm.load"(%[[v121]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v123:.*]] = "llvm.zext"(%[[v122]]) : (i8) -> i32
// CHECK-NEXT:         %[[v124:.*]] = "llvm.shl"(%[[v123]], %[[v20]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v125:.*]] = "llvm.or"(%[[v120]], %[[v124]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v126:.*]] = "llvm.add"(%[[v33]], %[[varg100_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v127:.*]] = "llvm.sext"(%[[v126]]) : (i32) -> i64
// CHECK-NEXT:         %[[v128:.*]] = "llvm.getelementptr"(%[[v45]], %[[v18]], %[[v127]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v125]], %[[v128]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v130:.*]] = "llvm.add"(%[[varg100_0]], %[[v12]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v130]]) [^[[bb100]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb104]]():
// CHECK-NEXT:         %[[v132:.*]] = "llvm.getelementptr"(%[[v45]], %[[v18]], %[[v16]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[varg87_0]], %[[v132]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v13]]) [^[[bb134:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb134]](%[[varg134_0:.*]] : i32):
// CHECK-NEXT:         %[[v136:.*]] = "llvm.icmp"(%[[varg134_0]], %[[v30]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v136]]) [^[[bb137:.*]], ^[[bb138:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb137]]():
// CHECK-NEXT:         %[[v140:.*]] = "llvm.mul"(%[[v33]], %[[varg134_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v141:.*]] = "llvm.sext"(%[[v140]]) : (i32) -> i64
// CHECK-NEXT:         %[[v142:.*]] = "llvm.getelementptr"(%[[v84]], %[[v141]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v143:.*]] = "llvm.load"(%[[v142]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v144:.*]] = "llvm.zext"(%[[v143]]) : (i8) -> i32
// CHECK-NEXT:         %[[v145:.*]] = "llvm.getelementptr"(%[[v142]], %[[v21]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v146:.*]] = "llvm.load"(%[[v145]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v147:.*]] = "llvm.zext"(%[[v146]]) : (i8) -> i32
// CHECK-NEXT:         %[[v148:.*]] = "llvm.shl"(%[[v147]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v149:.*]] = "llvm.or"(%[[v144]], %[[v148]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v150:.*]] = "llvm.getelementptr"(%[[v142]], %[[v23]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v151:.*]] = "llvm.load"(%[[v150]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v152:.*]] = "llvm.zext"(%[[v151]]) : (i8) -> i32
// CHECK-NEXT:         %[[v153:.*]] = "llvm.shl"(%[[v152]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v154:.*]] = "llvm.or"(%[[v149]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v155:.*]] = "llvm.getelementptr"(%[[v142]], %[[v25]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v156:.*]] = "llvm.load"(%[[v155]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v157:.*]] = "llvm.zext"(%[[v156]]) : (i8) -> i32
// CHECK-NEXT:         %[[v158:.*]] = "llvm.shl"(%[[v157]], %[[v20]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v159:.*]] = "llvm.or"(%[[v154]], %[[v158]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v160:.*]] = "llvm.add"(%[[v37]], %[[varg134_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v161:.*]] = "llvm.sext"(%[[v160]]) : (i32) -> i64
// CHECK-NEXT:         %[[v162:.*]] = "llvm.getelementptr"(%[[v45]], %[[v18]], %[[v161]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v159]], %[[v162]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v164:.*]] = "llvm.add"(%[[varg134_0]], %[[v12]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v164]]) [^[[bb134]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb138]]():
// CHECK-NEXT:         "llvm.br"(%[[v13]]) [^[[bb166:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb166]](%[[varg166_0:.*]] : i32):
// CHECK-NEXT:         %[[v168:.*]] = "llvm.icmp"(%[[varg166_0]], %[[v22]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v168]]) [^[[bb169:.*]], ^[[bb170:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb169]]():
// CHECK-NEXT:         %[[v172:.*]] = "llvm.sext"(%[[varg166_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v173:.*]] = "llvm.getelementptr"(%[[v45]], %[[v18]], %[[v172]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v174:.*]] = "llvm.load"(%[[v173]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v176:.*]] = "llvm.getelementptr"(%[[v46]], %[[v18]], %[[v172]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v174]], %[[v176]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v178:.*]] = "llvm.add"(%[[varg166_0]], %[[v12]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v178]]) [^[[bb166]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb170]]():
// CHECK-NEXT:         "llvm.br"(%[[v13]]) [^[[bb180:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb180]](%[[varg180_0:.*]] : i32):
// CHECK-NEXT:         %[[v182:.*]] = "llvm.icmp"(%[[varg180_0]], %[[v31]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v182]]) [^[[bb183:.*]], ^[[bb184:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb183]]():
// CHECK-NEXT:         %[[v186:.*]] = "llvm.sext"(%[[v33]]) : (i32) -> i64
// CHECK-NEXT:         %[[v187:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v188:.*]] = "llvm.load"(%[[v187]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v189:.*]] = "llvm.sext"(%[[v13]]) : (i32) -> i64
// CHECK-NEXT:         %[[v190:.*]] = "llvm.getelementptr"(%[[v46]], %[[v189]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v191:.*]] = "llvm.load"(%[[v190]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v192:.*]] = "llvm.add"(%[[v191]], %[[v188]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v192]], %[[v190]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v195:.*]] = "llvm.getelementptr"(%[[v46]], %[[v189]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v196:.*]] = "llvm.load"(%[[v195]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v197:.*]] = "llvm.sext"(%[[v34]]) : (i32) -> i64
// CHECK-NEXT:         %[[v198:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v199:.*]] = "llvm.load"(%[[v198]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v200:.*]] = "llvm.xor"(%[[v199]], %[[v196]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v200]], %[[v198]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v203:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v204:.*]] = "llvm.load"(%[[v203]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v205:.*]] = "llvm.shl"(%[[v204]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v206:.*]] = "llvm.sub"(%[[v14]], %[[v22]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v207:.*]] = "llvm.lshr"(%[[v204]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v208:.*]] = "llvm.or"(%[[v205]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v210:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v208]], %[[v210]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v213:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v214:.*]] = "llvm.load"(%[[v213]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v215:.*]] = "llvm.sext"(%[[v24]]) : (i32) -> i64
// CHECK-NEXT:         %[[v216:.*]] = "llvm.getelementptr"(%[[v46]], %[[v215]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v217:.*]] = "llvm.load"(%[[v216]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v218:.*]] = "llvm.add"(%[[v217]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v218]], %[[v216]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v221:.*]] = "llvm.getelementptr"(%[[v46]], %[[v215]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v222:.*]] = "llvm.load"(%[[v221]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v224:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v225:.*]] = "llvm.load"(%[[v224]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v226:.*]] = "llvm.xor"(%[[v225]], %[[v222]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v226]], %[[v224]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v229:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v230:.*]] = "llvm.load"(%[[v229]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v231:.*]] = "llvm.shl"(%[[v230]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v232:.*]] = "llvm.sub"(%[[v14]], %[[v34]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v233:.*]] = "llvm.lshr"(%[[v230]], %[[v232]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v234:.*]] = "llvm.or"(%[[v231]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v236:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v234]], %[[v236]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v239:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v240:.*]] = "llvm.load"(%[[v239]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v242:.*]] = "llvm.getelementptr"(%[[v46]], %[[v189]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v243:.*]] = "llvm.load"(%[[v242]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v244:.*]] = "llvm.add"(%[[v243]], %[[v240]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v244]], %[[v242]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v247:.*]] = "llvm.getelementptr"(%[[v46]], %[[v189]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v248:.*]] = "llvm.load"(%[[v247]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v250:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v251:.*]] = "llvm.load"(%[[v250]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v252:.*]] = "llvm.xor"(%[[v251]], %[[v248]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v252]], %[[v250]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v255:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v256:.*]] = "llvm.load"(%[[v255]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v257:.*]] = "llvm.shl"(%[[v256]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v258:.*]] = "llvm.sub"(%[[v14]], %[[v24]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v259:.*]] = "llvm.lshr"(%[[v256]], %[[v258]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v260:.*]] = "llvm.or"(%[[v257]], %[[v259]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v262:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v260]], %[[v262]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v265:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v266:.*]] = "llvm.load"(%[[v265]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v268:.*]] = "llvm.getelementptr"(%[[v46]], %[[v215]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v269:.*]] = "llvm.load"(%[[v268]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v270:.*]] = "llvm.add"(%[[v269]], %[[v266]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v270]], %[[v268]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v273:.*]] = "llvm.getelementptr"(%[[v46]], %[[v215]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v274:.*]] = "llvm.load"(%[[v273]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v276:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v277:.*]] = "llvm.load"(%[[v276]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v278:.*]] = "llvm.xor"(%[[v277]], %[[v274]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v278]], %[[v276]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v281:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v282:.*]] = "llvm.load"(%[[v281]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v283:.*]] = "llvm.shl"(%[[v282]], %[[v35]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v284:.*]] = "llvm.sub"(%[[v14]], %[[v35]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v285:.*]] = "llvm.lshr"(%[[v282]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v286:.*]] = "llvm.or"(%[[v283]], %[[v285]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v288:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v286]], %[[v288]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v290:.*]] = "llvm.sext"(%[[v36]]) : (i32) -> i64
// CHECK-NEXT:         %[[v291:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v292:.*]] = "llvm.load"(%[[v291]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v293:.*]] = "llvm.sext"(%[[v12]]) : (i32) -> i64
// CHECK-NEXT:         %[[v294:.*]] = "llvm.getelementptr"(%[[v46]], %[[v293]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v295:.*]] = "llvm.load"(%[[v294]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v296:.*]] = "llvm.add"(%[[v295]], %[[v292]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v296]], %[[v294]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v299:.*]] = "llvm.getelementptr"(%[[v46]], %[[v293]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v300:.*]] = "llvm.load"(%[[v299]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v301:.*]] = "llvm.sext"(%[[v37]]) : (i32) -> i64
// CHECK-NEXT:         %[[v302:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v303:.*]] = "llvm.load"(%[[v302]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v304:.*]] = "llvm.xor"(%[[v303]], %[[v300]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v304]], %[[v302]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v307:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v308:.*]] = "llvm.load"(%[[v307]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v309:.*]] = "llvm.shl"(%[[v308]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v311:.*]] = "llvm.lshr"(%[[v308]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v312:.*]] = "llvm.or"(%[[v309]], %[[v311]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v314:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v312]], %[[v314]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v317:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v318:.*]] = "llvm.load"(%[[v317]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v319:.*]] = "llvm.sext"(%[[v38]]) : (i32) -> i64
// CHECK-NEXT:         %[[v320:.*]] = "llvm.getelementptr"(%[[v46]], %[[v319]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v321:.*]] = "llvm.load"(%[[v320]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v322:.*]] = "llvm.add"(%[[v321]], %[[v318]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v322]], %[[v320]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v325:.*]] = "llvm.getelementptr"(%[[v46]], %[[v319]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v326:.*]] = "llvm.load"(%[[v325]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v328:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v329:.*]] = "llvm.load"(%[[v328]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v330:.*]] = "llvm.xor"(%[[v329]], %[[v326]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v330]], %[[v328]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v333:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v334:.*]] = "llvm.load"(%[[v333]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v335:.*]] = "llvm.shl"(%[[v334]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v337:.*]] = "llvm.lshr"(%[[v334]], %[[v232]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v338:.*]] = "llvm.or"(%[[v335]], %[[v337]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v340:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v338]], %[[v340]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v343:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v344:.*]] = "llvm.load"(%[[v343]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v346:.*]] = "llvm.getelementptr"(%[[v46]], %[[v293]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v347:.*]] = "llvm.load"(%[[v346]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v348:.*]] = "llvm.add"(%[[v347]], %[[v344]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v348]], %[[v346]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v351:.*]] = "llvm.getelementptr"(%[[v46]], %[[v293]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v352:.*]] = "llvm.load"(%[[v351]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v354:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v355:.*]] = "llvm.load"(%[[v354]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v356:.*]] = "llvm.xor"(%[[v355]], %[[v352]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v356]], %[[v354]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v359:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v360:.*]] = "llvm.load"(%[[v359]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v361:.*]] = "llvm.shl"(%[[v360]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v363:.*]] = "llvm.lshr"(%[[v360]], %[[v258]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v364:.*]] = "llvm.or"(%[[v361]], %[[v363]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v366:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v364]], %[[v366]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v369:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v370:.*]] = "llvm.load"(%[[v369]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v372:.*]] = "llvm.getelementptr"(%[[v46]], %[[v319]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v373:.*]] = "llvm.load"(%[[v372]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v374:.*]] = "llvm.add"(%[[v373]], %[[v370]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v374]], %[[v372]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v377:.*]] = "llvm.getelementptr"(%[[v46]], %[[v319]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v378:.*]] = "llvm.load"(%[[v377]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v380:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v381:.*]] = "llvm.load"(%[[v380]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v382:.*]] = "llvm.xor"(%[[v381]], %[[v378]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v382]], %[[v380]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v385:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v386:.*]] = "llvm.load"(%[[v385]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v387:.*]] = "llvm.shl"(%[[v386]], %[[v35]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v389:.*]] = "llvm.lshr"(%[[v386]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v390:.*]] = "llvm.or"(%[[v387]], %[[v389]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v392:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v390]], %[[v392]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v394:.*]] = "llvm.sext"(%[[v39]]) : (i32) -> i64
// CHECK-NEXT:         %[[v395:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v396:.*]] = "llvm.load"(%[[v395]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v397:.*]] = "llvm.sext"(%[[v40]]) : (i32) -> i64
// CHECK-NEXT:         %[[v398:.*]] = "llvm.getelementptr"(%[[v46]], %[[v397]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v399:.*]] = "llvm.load"(%[[v398]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v400:.*]] = "llvm.add"(%[[v399]], %[[v396]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v400]], %[[v398]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v403:.*]] = "llvm.getelementptr"(%[[v46]], %[[v397]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v404:.*]] = "llvm.load"(%[[v403]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v405:.*]] = "llvm.sext"(%[[v41]]) : (i32) -> i64
// CHECK-NEXT:         %[[v406:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v407:.*]] = "llvm.load"(%[[v406]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v408:.*]] = "llvm.xor"(%[[v407]], %[[v404]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v408]], %[[v406]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v411:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v412:.*]] = "llvm.load"(%[[v411]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v413:.*]] = "llvm.shl"(%[[v412]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v415:.*]] = "llvm.lshr"(%[[v412]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v416:.*]] = "llvm.or"(%[[v413]], %[[v415]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v418:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v416]], %[[v418]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v421:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v422:.*]] = "llvm.load"(%[[v421]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v423:.*]] = "llvm.sext"(%[[v31]]) : (i32) -> i64
// CHECK-NEXT:         %[[v424:.*]] = "llvm.getelementptr"(%[[v46]], %[[v423]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v425:.*]] = "llvm.load"(%[[v424]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v426:.*]] = "llvm.add"(%[[v425]], %[[v422]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v426]], %[[v424]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v429:.*]] = "llvm.getelementptr"(%[[v46]], %[[v423]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v430:.*]] = "llvm.load"(%[[v429]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v432:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v433:.*]] = "llvm.load"(%[[v432]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v434:.*]] = "llvm.xor"(%[[v433]], %[[v430]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v434]], %[[v432]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v437:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v438:.*]] = "llvm.load"(%[[v437]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v439:.*]] = "llvm.shl"(%[[v438]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v441:.*]] = "llvm.lshr"(%[[v438]], %[[v232]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v442:.*]] = "llvm.or"(%[[v439]], %[[v441]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v444:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v442]], %[[v444]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v447:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v448:.*]] = "llvm.load"(%[[v447]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v450:.*]] = "llvm.getelementptr"(%[[v46]], %[[v397]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v451:.*]] = "llvm.load"(%[[v450]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v452:.*]] = "llvm.add"(%[[v451]], %[[v448]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v452]], %[[v450]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v455:.*]] = "llvm.getelementptr"(%[[v46]], %[[v397]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v456:.*]] = "llvm.load"(%[[v455]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v458:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v459:.*]] = "llvm.load"(%[[v458]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v460:.*]] = "llvm.xor"(%[[v459]], %[[v456]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v460]], %[[v458]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v463:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v464:.*]] = "llvm.load"(%[[v463]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v465:.*]] = "llvm.shl"(%[[v464]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v467:.*]] = "llvm.lshr"(%[[v464]], %[[v258]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v468:.*]] = "llvm.or"(%[[v465]], %[[v467]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v470:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v468]], %[[v470]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v473:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v474:.*]] = "llvm.load"(%[[v473]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v476:.*]] = "llvm.getelementptr"(%[[v46]], %[[v423]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v477:.*]] = "llvm.load"(%[[v476]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v478:.*]] = "llvm.add"(%[[v477]], %[[v474]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v478]], %[[v476]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v481:.*]] = "llvm.getelementptr"(%[[v46]], %[[v423]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v482:.*]] = "llvm.load"(%[[v481]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v484:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v485:.*]] = "llvm.load"(%[[v484]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v486:.*]] = "llvm.xor"(%[[v485]], %[[v482]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v486]], %[[v484]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v489:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v490:.*]] = "llvm.load"(%[[v489]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v491:.*]] = "llvm.shl"(%[[v490]], %[[v35]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v493:.*]] = "llvm.lshr"(%[[v490]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v494:.*]] = "llvm.or"(%[[v491]], %[[v493]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v496:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v494]], %[[v496]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v498:.*]] = "llvm.sext"(%[[v35]]) : (i32) -> i64
// CHECK-NEXT:         %[[v499:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v500:.*]] = "llvm.load"(%[[v499]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v501:.*]] = "llvm.sext"(%[[v30]]) : (i32) -> i64
// CHECK-NEXT:         %[[v502:.*]] = "llvm.getelementptr"(%[[v46]], %[[v501]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v503:.*]] = "llvm.load"(%[[v502]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v504:.*]] = "llvm.add"(%[[v503]], %[[v500]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v504]], %[[v502]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v507:.*]] = "llvm.getelementptr"(%[[v46]], %[[v501]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v508:.*]] = "llvm.load"(%[[v507]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v509:.*]] = "llvm.sext"(%[[v42]]) : (i32) -> i64
// CHECK-NEXT:         %[[v510:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v511:.*]] = "llvm.load"(%[[v510]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v512:.*]] = "llvm.xor"(%[[v511]], %[[v508]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v512]], %[[v510]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v515:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v516:.*]] = "llvm.load"(%[[v515]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v517:.*]] = "llvm.shl"(%[[v516]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v519:.*]] = "llvm.lshr"(%[[v516]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v520:.*]] = "llvm.or"(%[[v517]], %[[v519]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v522:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v520]], %[[v522]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v525:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v526:.*]] = "llvm.load"(%[[v525]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v527:.*]] = "llvm.sext"(%[[v43]]) : (i32) -> i64
// CHECK-NEXT:         %[[v528:.*]] = "llvm.getelementptr"(%[[v46]], %[[v527]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v529:.*]] = "llvm.load"(%[[v528]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v530:.*]] = "llvm.add"(%[[v529]], %[[v526]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v530]], %[[v528]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v533:.*]] = "llvm.getelementptr"(%[[v46]], %[[v527]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v534:.*]] = "llvm.load"(%[[v533]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v536:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v537:.*]] = "llvm.load"(%[[v536]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v538:.*]] = "llvm.xor"(%[[v537]], %[[v534]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v538]], %[[v536]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v541:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v542:.*]] = "llvm.load"(%[[v541]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v543:.*]] = "llvm.shl"(%[[v542]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v545:.*]] = "llvm.lshr"(%[[v542]], %[[v232]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v546:.*]] = "llvm.or"(%[[v543]], %[[v545]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v548:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v546]], %[[v548]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v551:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v552:.*]] = "llvm.load"(%[[v551]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v554:.*]] = "llvm.getelementptr"(%[[v46]], %[[v501]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v555:.*]] = "llvm.load"(%[[v554]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v556:.*]] = "llvm.add"(%[[v555]], %[[v552]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v556]], %[[v554]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v559:.*]] = "llvm.getelementptr"(%[[v46]], %[[v501]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v560:.*]] = "llvm.load"(%[[v559]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v562:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v563:.*]] = "llvm.load"(%[[v562]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v564:.*]] = "llvm.xor"(%[[v563]], %[[v560]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v564]], %[[v562]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v567:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v568:.*]] = "llvm.load"(%[[v567]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v569:.*]] = "llvm.shl"(%[[v568]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v571:.*]] = "llvm.lshr"(%[[v568]], %[[v258]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v572:.*]] = "llvm.or"(%[[v569]], %[[v571]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v574:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v572]], %[[v574]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v577:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v578:.*]] = "llvm.load"(%[[v577]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v580:.*]] = "llvm.getelementptr"(%[[v46]], %[[v527]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v581:.*]] = "llvm.load"(%[[v580]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v582:.*]] = "llvm.add"(%[[v581]], %[[v578]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v582]], %[[v580]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v585:.*]] = "llvm.getelementptr"(%[[v46]], %[[v527]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v586:.*]] = "llvm.load"(%[[v585]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v588:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v589:.*]] = "llvm.load"(%[[v588]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v590:.*]] = "llvm.xor"(%[[v589]], %[[v586]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v590]], %[[v588]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v593:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v594:.*]] = "llvm.load"(%[[v593]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v595:.*]] = "llvm.shl"(%[[v594]], %[[v35]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v597:.*]] = "llvm.lshr"(%[[v594]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v598:.*]] = "llvm.or"(%[[v595]], %[[v597]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v600:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v598]], %[[v600]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v603:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v604:.*]] = "llvm.load"(%[[v603]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v606:.*]] = "llvm.getelementptr"(%[[v46]], %[[v189]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v607:.*]] = "llvm.load"(%[[v606]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v608:.*]] = "llvm.add"(%[[v607]], %[[v604]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v608]], %[[v606]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v611:.*]] = "llvm.getelementptr"(%[[v46]], %[[v189]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v612:.*]] = "llvm.load"(%[[v611]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v614:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v615:.*]] = "llvm.load"(%[[v614]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v616:.*]] = "llvm.xor"(%[[v615]], %[[v612]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v616]], %[[v614]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v619:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v620:.*]] = "llvm.load"(%[[v619]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v621:.*]] = "llvm.shl"(%[[v620]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v623:.*]] = "llvm.lshr"(%[[v620]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v624:.*]] = "llvm.or"(%[[v621]], %[[v623]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v626:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v624]], %[[v626]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v629:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v630:.*]] = "llvm.load"(%[[v629]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v632:.*]] = "llvm.getelementptr"(%[[v46]], %[[v423]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v633:.*]] = "llvm.load"(%[[v632]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v634:.*]] = "llvm.add"(%[[v633]], %[[v630]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v634]], %[[v632]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v637:.*]] = "llvm.getelementptr"(%[[v46]], %[[v423]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v638:.*]] = "llvm.load"(%[[v637]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v640:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v641:.*]] = "llvm.load"(%[[v640]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v642:.*]] = "llvm.xor"(%[[v641]], %[[v638]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v642]], %[[v640]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v645:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v646:.*]] = "llvm.load"(%[[v645]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v647:.*]] = "llvm.shl"(%[[v646]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v649:.*]] = "llvm.lshr"(%[[v646]], %[[v232]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v650:.*]] = "llvm.or"(%[[v647]], %[[v649]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v652:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v650]], %[[v652]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v655:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v656:.*]] = "llvm.load"(%[[v655]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v658:.*]] = "llvm.getelementptr"(%[[v46]], %[[v189]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v659:.*]] = "llvm.load"(%[[v658]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v660:.*]] = "llvm.add"(%[[v659]], %[[v656]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v660]], %[[v658]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v663:.*]] = "llvm.getelementptr"(%[[v46]], %[[v189]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v664:.*]] = "llvm.load"(%[[v663]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v666:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v667:.*]] = "llvm.load"(%[[v666]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v668:.*]] = "llvm.xor"(%[[v667]], %[[v664]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v668]], %[[v666]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v671:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v672:.*]] = "llvm.load"(%[[v671]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v673:.*]] = "llvm.shl"(%[[v672]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v675:.*]] = "llvm.lshr"(%[[v672]], %[[v258]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v676:.*]] = "llvm.or"(%[[v673]], %[[v675]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v678:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v676]], %[[v678]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v681:.*]] = "llvm.getelementptr"(%[[v46]], %[[v509]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v682:.*]] = "llvm.load"(%[[v681]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v684:.*]] = "llvm.getelementptr"(%[[v46]], %[[v423]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v685:.*]] = "llvm.load"(%[[v684]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v686:.*]] = "llvm.add"(%[[v685]], %[[v682]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v686]], %[[v684]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v689:.*]] = "llvm.getelementptr"(%[[v46]], %[[v423]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v690:.*]] = "llvm.load"(%[[v689]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v692:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v693:.*]] = "llvm.load"(%[[v692]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v694:.*]] = "llvm.xor"(%[[v693]], %[[v690]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v694]], %[[v692]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v697:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v698:.*]] = "llvm.load"(%[[v697]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v699:.*]] = "llvm.shl"(%[[v698]], %[[v35]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v701:.*]] = "llvm.lshr"(%[[v698]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v702:.*]] = "llvm.or"(%[[v699]], %[[v701]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v704:.*]] = "llvm.getelementptr"(%[[v46]], %[[v290]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v702]], %[[v704]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v707:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v708:.*]] = "llvm.load"(%[[v707]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v710:.*]] = "llvm.getelementptr"(%[[v46]], %[[v293]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v711:.*]] = "llvm.load"(%[[v710]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v712:.*]] = "llvm.add"(%[[v711]], %[[v708]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v712]], %[[v710]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v715:.*]] = "llvm.getelementptr"(%[[v46]], %[[v293]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v716:.*]] = "llvm.load"(%[[v715]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v718:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v719:.*]] = "llvm.load"(%[[v718]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v720:.*]] = "llvm.xor"(%[[v719]], %[[v716]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v720]], %[[v718]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v723:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v724:.*]] = "llvm.load"(%[[v723]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v725:.*]] = "llvm.shl"(%[[v724]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v727:.*]] = "llvm.lshr"(%[[v724]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v728:.*]] = "llvm.or"(%[[v725]], %[[v727]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v730:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v728]], %[[v730]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v733:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v734:.*]] = "llvm.load"(%[[v733]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v736:.*]] = "llvm.getelementptr"(%[[v46]], %[[v527]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v737:.*]] = "llvm.load"(%[[v736]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v738:.*]] = "llvm.add"(%[[v737]], %[[v734]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v738]], %[[v736]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v741:.*]] = "llvm.getelementptr"(%[[v46]], %[[v527]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v742:.*]] = "llvm.load"(%[[v741]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v744:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v745:.*]] = "llvm.load"(%[[v744]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v746:.*]] = "llvm.xor"(%[[v745]], %[[v742]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v746]], %[[v744]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v749:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v750:.*]] = "llvm.load"(%[[v749]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v751:.*]] = "llvm.shl"(%[[v750]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v753:.*]] = "llvm.lshr"(%[[v750]], %[[v232]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v754:.*]] = "llvm.or"(%[[v751]], %[[v753]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v756:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v754]], %[[v756]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v759:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v760:.*]] = "llvm.load"(%[[v759]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v762:.*]] = "llvm.getelementptr"(%[[v46]], %[[v293]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v763:.*]] = "llvm.load"(%[[v762]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v764:.*]] = "llvm.add"(%[[v763]], %[[v760]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v764]], %[[v762]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v767:.*]] = "llvm.getelementptr"(%[[v46]], %[[v293]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v768:.*]] = "llvm.load"(%[[v767]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v770:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v771:.*]] = "llvm.load"(%[[v770]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v772:.*]] = "llvm.xor"(%[[v771]], %[[v768]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v772]], %[[v770]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v775:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v776:.*]] = "llvm.load"(%[[v775]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v777:.*]] = "llvm.shl"(%[[v776]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v779:.*]] = "llvm.lshr"(%[[v776]], %[[v258]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v780:.*]] = "llvm.or"(%[[v777]], %[[v779]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v782:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v780]], %[[v782]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v785:.*]] = "llvm.getelementptr"(%[[v46]], %[[v197]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v786:.*]] = "llvm.load"(%[[v785]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v788:.*]] = "llvm.getelementptr"(%[[v46]], %[[v527]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v789:.*]] = "llvm.load"(%[[v788]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v790:.*]] = "llvm.add"(%[[v789]], %[[v786]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v790]], %[[v788]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v793:.*]] = "llvm.getelementptr"(%[[v46]], %[[v527]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v794:.*]] = "llvm.load"(%[[v793]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v796:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v797:.*]] = "llvm.load"(%[[v796]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v798:.*]] = "llvm.xor"(%[[v797]], %[[v794]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v798]], %[[v796]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v801:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v802:.*]] = "llvm.load"(%[[v801]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v803:.*]] = "llvm.shl"(%[[v802]], %[[v35]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v805:.*]] = "llvm.lshr"(%[[v802]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v806:.*]] = "llvm.or"(%[[v803]], %[[v805]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v808:.*]] = "llvm.getelementptr"(%[[v46]], %[[v394]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v806]], %[[v808]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v811:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v812:.*]] = "llvm.load"(%[[v811]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v814:.*]] = "llvm.getelementptr"(%[[v46]], %[[v397]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v815:.*]] = "llvm.load"(%[[v814]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v816:.*]] = "llvm.add"(%[[v815]], %[[v812]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v816]], %[[v814]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v819:.*]] = "llvm.getelementptr"(%[[v46]], %[[v397]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v820:.*]] = "llvm.load"(%[[v819]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v822:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v823:.*]] = "llvm.load"(%[[v822]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v824:.*]] = "llvm.xor"(%[[v823]], %[[v820]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v824]], %[[v822]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v827:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v828:.*]] = "llvm.load"(%[[v827]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v829:.*]] = "llvm.shl"(%[[v828]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v831:.*]] = "llvm.lshr"(%[[v828]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v832:.*]] = "llvm.or"(%[[v829]], %[[v831]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v834:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v832]], %[[v834]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v837:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v838:.*]] = "llvm.load"(%[[v837]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v840:.*]] = "llvm.getelementptr"(%[[v46]], %[[v215]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v841:.*]] = "llvm.load"(%[[v840]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v842:.*]] = "llvm.add"(%[[v841]], %[[v838]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v842]], %[[v840]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v845:.*]] = "llvm.getelementptr"(%[[v46]], %[[v215]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v846:.*]] = "llvm.load"(%[[v845]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v848:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v849:.*]] = "llvm.load"(%[[v848]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v850:.*]] = "llvm.xor"(%[[v849]], %[[v846]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v850]], %[[v848]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v853:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v854:.*]] = "llvm.load"(%[[v853]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v855:.*]] = "llvm.shl"(%[[v854]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v857:.*]] = "llvm.lshr"(%[[v854]], %[[v232]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v858:.*]] = "llvm.or"(%[[v855]], %[[v857]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v860:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v858]], %[[v860]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v863:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v864:.*]] = "llvm.load"(%[[v863]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v866:.*]] = "llvm.getelementptr"(%[[v46]], %[[v397]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v867:.*]] = "llvm.load"(%[[v866]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v868:.*]] = "llvm.add"(%[[v867]], %[[v864]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v868]], %[[v866]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v871:.*]] = "llvm.getelementptr"(%[[v46]], %[[v397]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v872:.*]] = "llvm.load"(%[[v871]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v874:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v875:.*]] = "llvm.load"(%[[v874]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v876:.*]] = "llvm.xor"(%[[v875]], %[[v872]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v876]], %[[v874]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v879:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v880:.*]] = "llvm.load"(%[[v879]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v881:.*]] = "llvm.shl"(%[[v880]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v883:.*]] = "llvm.lshr"(%[[v880]], %[[v258]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v884:.*]] = "llvm.or"(%[[v881]], %[[v883]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v886:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v884]], %[[v886]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v889:.*]] = "llvm.getelementptr"(%[[v46]], %[[v301]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v890:.*]] = "llvm.load"(%[[v889]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v892:.*]] = "llvm.getelementptr"(%[[v46]], %[[v215]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v893:.*]] = "llvm.load"(%[[v892]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v894:.*]] = "llvm.add"(%[[v893]], %[[v890]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v894]], %[[v892]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v897:.*]] = "llvm.getelementptr"(%[[v46]], %[[v215]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v898:.*]] = "llvm.load"(%[[v897]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v900:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v901:.*]] = "llvm.load"(%[[v900]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v902:.*]] = "llvm.xor"(%[[v901]], %[[v898]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v902]], %[[v900]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v905:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v906:.*]] = "llvm.load"(%[[v905]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v907:.*]] = "llvm.shl"(%[[v906]], %[[v35]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v909:.*]] = "llvm.lshr"(%[[v906]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v910:.*]] = "llvm.or"(%[[v907]], %[[v909]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v912:.*]] = "llvm.getelementptr"(%[[v46]], %[[v498]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v910]], %[[v912]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v915:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v916:.*]] = "llvm.load"(%[[v915]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v918:.*]] = "llvm.getelementptr"(%[[v46]], %[[v501]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v919:.*]] = "llvm.load"(%[[v918]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v920:.*]] = "llvm.add"(%[[v919]], %[[v916]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v920]], %[[v918]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v923:.*]] = "llvm.getelementptr"(%[[v46]], %[[v501]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v924:.*]] = "llvm.load"(%[[v923]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v926:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v927:.*]] = "llvm.load"(%[[v926]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v928:.*]] = "llvm.xor"(%[[v927]], %[[v924]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v928]], %[[v926]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v931:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v932:.*]] = "llvm.load"(%[[v931]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v933:.*]] = "llvm.shl"(%[[v932]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v935:.*]] = "llvm.lshr"(%[[v932]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v936:.*]] = "llvm.or"(%[[v933]], %[[v935]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v938:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v936]], %[[v938]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v941:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v942:.*]] = "llvm.load"(%[[v941]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v944:.*]] = "llvm.getelementptr"(%[[v46]], %[[v319]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v945:.*]] = "llvm.load"(%[[v944]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v946:.*]] = "llvm.add"(%[[v945]], %[[v942]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v946]], %[[v944]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v949:.*]] = "llvm.getelementptr"(%[[v46]], %[[v319]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v950:.*]] = "llvm.load"(%[[v949]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v952:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v953:.*]] = "llvm.load"(%[[v952]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v954:.*]] = "llvm.xor"(%[[v953]], %[[v950]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v954]], %[[v952]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v957:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v958:.*]] = "llvm.load"(%[[v957]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v959:.*]] = "llvm.shl"(%[[v958]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v961:.*]] = "llvm.lshr"(%[[v958]], %[[v232]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v962:.*]] = "llvm.or"(%[[v959]], %[[v961]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v964:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v962]], %[[v964]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v967:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v968:.*]] = "llvm.load"(%[[v967]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v970:.*]] = "llvm.getelementptr"(%[[v46]], %[[v501]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v971:.*]] = "llvm.load"(%[[v970]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v972:.*]] = "llvm.add"(%[[v971]], %[[v968]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v972]], %[[v970]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v975:.*]] = "llvm.getelementptr"(%[[v46]], %[[v501]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v976:.*]] = "llvm.load"(%[[v975]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v978:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v979:.*]] = "llvm.load"(%[[v978]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v980:.*]] = "llvm.xor"(%[[v979]], %[[v976]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v980]], %[[v978]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v983:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v984:.*]] = "llvm.load"(%[[v983]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v985:.*]] = "llvm.shl"(%[[v984]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v987:.*]] = "llvm.lshr"(%[[v984]], %[[v258]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v988:.*]] = "llvm.or"(%[[v985]], %[[v987]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v990:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v988]], %[[v990]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v993:.*]] = "llvm.getelementptr"(%[[v46]], %[[v405]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v994:.*]] = "llvm.load"(%[[v993]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v996:.*]] = "llvm.getelementptr"(%[[v46]], %[[v319]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v997:.*]] = "llvm.load"(%[[v996]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v998:.*]] = "llvm.add"(%[[v997]], %[[v994]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v998]], %[[v996]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1001:.*]] = "llvm.getelementptr"(%[[v46]], %[[v319]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1002:.*]] = "llvm.load"(%[[v1001]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1004:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1005:.*]] = "llvm.load"(%[[v1004]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1006:.*]] = "llvm.xor"(%[[v1005]], %[[v1002]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v1006]], %[[v1004]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1009:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1010:.*]] = "llvm.load"(%[[v1009]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1011:.*]] = "llvm.shl"(%[[v1010]], %[[v35]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1013:.*]] = "llvm.lshr"(%[[v1010]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1014:.*]] = "llvm.or"(%[[v1011]], %[[v1013]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1016:.*]] = "llvm.getelementptr"(%[[v46]], %[[v186]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1014]], %[[v1016]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1018:.*]] = "llvm.add"(%[[varg180_0]], %[[v12]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v1018]]) [^[[bb180]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb184]]():
// CHECK-NEXT:         "llvm.br"(%[[v13]]) [^[[bb1020:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb1020]](%[[varg1020_0:.*]] : i32):
// CHECK-NEXT:         %[[v1022:.*]] = "llvm.icmp"(%[[varg1020_0]], %[[v22]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v1022]]) [^[[bb1023:.*]], ^[[bb1024:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb1023]]():
// CHECK-NEXT:         %[[v1026:.*]] = "llvm.mul"(%[[v33]], %[[varg1020_0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1027:.*]] = "llvm.sext"(%[[v1026]]) : (i32) -> i64
// CHECK-NEXT:         %[[v1028:.*]] = "llvm.getelementptr"(%[[v47]], %[[v1027]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1029:.*]] = "llvm.sext"(%[[varg1020_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v1030:.*]] = "llvm.getelementptr"(%[[v46]], %[[v18]], %[[v1029]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1031:.*]] = "llvm.load"(%[[v1030]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1033:.*]] = "llvm.getelementptr"(%[[v45]], %[[v18]], %[[v1029]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1034:.*]] = "llvm.load"(%[[v1033]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1035:.*]] = "llvm.add"(%[[v1031]], %[[v1034]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1036:.*]] = "llvm.trunc"(%[[v1035]]) : (i32) -> i8
// CHECK-NEXT:         "llvm.store"(%[[v1036]], %[[v1028]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1038:.*]] = "llvm.lshr"(%[[v1035]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1039:.*]] = "llvm.trunc"(%[[v1038]]) : (i32) -> i8
// CHECK-NEXT:         %[[v1040:.*]] = "llvm.getelementptr"(%[[v1028]], %[[v21]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1039]], %[[v1040]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1042:.*]] = "llvm.lshr"(%[[v1035]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1043:.*]] = "llvm.trunc"(%[[v1042]]) : (i32) -> i8
// CHECK-NEXT:         %[[v1044:.*]] = "llvm.getelementptr"(%[[v1028]], %[[v23]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1043]], %[[v1044]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1046:.*]] = "llvm.lshr"(%[[v1035]], %[[v20]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1047:.*]] = "llvm.trunc"(%[[v1046]]) : (i32) -> i8
// CHECK-NEXT:         %[[v1048:.*]] = "llvm.getelementptr"(%[[v1028]], %[[v25]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1047]], %[[v1048]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1050:.*]] = "llvm.add"(%[[varg1020_0]], %[[v12]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v1050]]) [^[[bb1020]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb1024]]():
// CHECK-NEXT:         %[[v1052:.*]] = "llvm.add"(%[[varg87_0]], %[[v12]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1053:.*]] = "llvm.sub"(%[[v19]], %[[varg87_1]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[v1054:.*]] = "llvm.icmp"(%[[v1053]], %[[v32]]) <{"predicate" = 8 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v1054]], %[[v1053]]) [^[[bb1055:.*]], ^[[bb1056:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
// CHECK-NEXT:       ^[[bb1055]]():
// CHECK-NEXT:         "llvm.br"(%[[v32]]) [^[[bb1056]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb1056]](%[[varg1056_0:.*]] : i64):
// CHECK-NEXT:         "llvm.br"(%[[v18]]) [^[[bb1059:.*]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb1059]](%[[varg1059_0:.*]] : i64):
// CHECK-NEXT:         %[[v1061:.*]] = "llvm.icmp"(%[[varg1059_0]], %[[varg1056_0]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v1061]]) [^[[bb1062:.*]], ^[[bb1063:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb1062]]():
// CHECK-NEXT:         %[[v1065:.*]] = "llvm.add"(%[[varg87_1]], %[[varg1059_0]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[v1066:.*]] = "llvm.getelementptr"(%[[v85]], %[[v1065]]) <{"elem_type" = i8, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1067:.*]] = "llvm.load"(%[[v1066]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1068:.*]] = "llvm.zext"(%[[v1067]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1069:.*]] = "llvm.getelementptr"(%[[v47]], %[[v18]], %[[varg1059_0]]) <{"elem_type" = !llvm.array<64 x i8>, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1070:.*]] = "llvm.load"(%[[v1069]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1071:.*]] = "llvm.zext"(%[[v1070]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1072:.*]] = "llvm.xor"(%[[v1068]], %[[v1071]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1073:.*]] = "llvm.trunc"(%[[v1072]]) : (i32) -> i8
// CHECK-NEXT:         %[[v1075:.*]] = "llvm.getelementptr"(%[[v86]], %[[v1065]]) <{"elem_type" = i8, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1073]], %[[v1075]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1077:.*]] = "llvm.add"(%[[varg1059_0]], %[[v21]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v1077]]) [^[[bb1059]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb1063]]():
// CHECK-NEXT:         %[[v1079:.*]] = "llvm.add"(%[[varg87_1]], %[[varg1056_0]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v1052]], %[[v1079]]) [^[[bb87]]] : (i32, i64) -> ()
// CHECK-NEXT:       ^[[bb91]]():
// CHECK-NEXT:         %[[v1081:.*]] = "llvm.getelementptr"(%[[v51]], %[[v18]], %[[v18]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1082:.*]] = "llvm.load"(%[[v1081]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1083:.*]] = "llvm.zext"(%[[v1082]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1084:.*]] = "llvm.shl"(%[[v1083]], %[[v20]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1085:.*]] = "llvm.getelementptr"(%[[v51]], %[[v18]], %[[v21]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1086:.*]] = "llvm.load"(%[[v1085]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1087:.*]] = "llvm.zext"(%[[v1086]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1088:.*]] = "llvm.shl"(%[[v1087]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1089:.*]] = "llvm.or"(%[[v1084]], %[[v1088]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1090:.*]] = "llvm.getelementptr"(%[[v51]], %[[v18]], %[[v23]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1091:.*]] = "llvm.load"(%[[v1090]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1092:.*]] = "llvm.zext"(%[[v1091]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1093:.*]] = "llvm.shl"(%[[v1092]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1094:.*]] = "llvm.or"(%[[v1089]], %[[v1093]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1095:.*]] = "llvm.getelementptr"(%[[v51]], %[[v18]], %[[v25]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v1096:.*]] = "llvm.load"(%[[v1095]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v1097:.*]] = "llvm.zext"(%[[v1096]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1098:.*]] = "llvm.or"(%[[v1094]], %[[v1097]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.return"(%[[v1098]]) : (i32) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "o", "dlti.legal_int_widths" = array<i32: 32, 64>, "dlti.stack_alignment" = 128 : i64, "dlti.function_pointer_alignment" = #dlti.function_pointer_alignment<32, function_dependent = true>>, "llvm.ident" = "Homebrew clang version 22.1.7", "llvm.module_asm" = [], "llvm.target_triple" = "arm64-apple-macosx26.0.0"} : () -> ()
