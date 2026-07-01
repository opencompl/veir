// RUN: ./Tools/vcc -O --emit-mlir %s -o - | filecheck %s
// RUN: ./Tools/vcc -c %s -o %t.o
// RUN: test -s %t.o
// RUN: ./Tools/vcc -S %s -o %t.s
// RUN: test -s %t.s
/*
    An implementation of the ChaCha20 stream cipher block function (RFC 8439).
    Some refrences:
    - Algorithm: https://cr.yp.to/chacha.htmlhttps://cr.yp.to/chacha/chacha-20080120.pdf
    - RFC 8439: https://datatracker.ietf.org/doc/html/rfc8439

    The structure (state matrix, quarter-round, double-round etc.) follows the public RFC, analog to
    the reference Python implementation at https://github.com/ph4r05/py-chacha20poly1305 (chacha.py).

    Layers:
      - quarter_round: the basic mixing step on four state words
      - chacha20_block: 20 rounds over the 16-word state, producing 64 keystream bytes

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
__attribute__((always_inline)) static void quarter_round(uint32_t *x, int a, int b, int c, int d) {
    x[a]+= x[b]; x[d]^= x[a]; x[d] = rotl32(x[d],16);
    x[c]+= x[d]; x[b]^= x[c]; x[b] = rotl32(x[b],12);
    x[a]+= x[b]; x[d]^= x[a]; x[d] = rotl32(x[d],8);
    x[c]+= x[d]; x[b]^= x[c]; x[b] = rotl32(x[b],7);
}

// produces one 64-byte ChaCha20 keystream block into out
__attribute__((always_inline)) void chacha20_block(const uint8_t *key, uint32_t counter, const uint8_t *nonce, uint8_t *out,
                                                   uint32_t *state, uint32_t *x) {
    state[0] = 0x61707865; // these constants are the ASCII codes of "expand 32-byte k" and fixed in the algo.
    state[1] = 0x3320646e;
    state[2] = 0x79622d32;
    state[3] = 0x6b206574;
    for (long i = 0; i < 8; i++)
        state[4+i] = load32le(key + 4*i);
    state[12] = counter;
    for (long i = 0; i < 3; i++)
        state[13+i] = load32le(nonce + 4*i);

    for (long i = 0; i < 16; i++)
        x[i] = state[i];

    // 20 rounds (10 double rounds each 4 col. rounds then four diag.rounds)
    for (long i = 0; i < 10; i++) {
        quarter_round(x,0,4,8,12);
        quarter_round(x,1,5,9,13);
        quarter_round(x,2,6,10,14);
        quarter_round(x,3,7,11,15);
        quarter_round(x,0,5,10,15);
        quarter_round(x,1,6,11,12);
        quarter_round(x,2,7,8,13);
        quarter_round(x,3,4,9,14);
    }

    for (long i = 0; i < 16; i++)
        store32le(out + 4*i, x[i]+ state[i]);
}

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^[[bb4:[0-9]+]]():
// CHECK-NEXT:     "llvm.module_flags"() {{.*}} : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}"sym_name" = "chacha20_block"{{.*}}}> ({
// CHECK-NEXT:       ^[[bb7:[0-9]+]](%[[varg7_0:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_1:[a-zA-Z0-9_]+]] : i32, %[[varg7_2:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_3:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_4:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_5:[a-zA-Z0-9_]+]] : !llvm.ptr):
// CHECK-NEXT:         %[[v8:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:         %[[v9:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1634760805 : i32}> : () -> i32
// CHECK-NEXT:         %[[v10:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[v11:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 857760878 : i32}> : () -> i32
// CHECK-NEXT:         %[[v12:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:         %[[v13:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2036477234 : i32}> : () -> i32
// CHECK-NEXT:         %[[v14:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK-NEXT:         %[[v15:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1797285236 : i32}> : () -> i32
// CHECK-NEXT:         %[[v16:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 8 : i64}> : () -> i64
// CHECK-NEXT:         %[[v17:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 12 : i64}> : () -> i64
// CHECK-NEXT:         %[[v18:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 16 : i64}> : () -> i64
// CHECK-NEXT:         %[[v19:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 10 : i64}> : () -> i64
// CHECK-NEXT:         %[[v20:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
// CHECK-NEXT:         %[[v21:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
// CHECK-NEXT:         %[[v22:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
// CHECK-NEXT:         %[[v23:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 24 : i32}> : () -> i32
// CHECK-NEXT:         %[[v24:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
// CHECK-NEXT:         %[[v25:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         %[[v26:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK-NEXT:         %[[v27:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
// CHECK-NEXT:         %[[v28:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:         %[[v29:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK-NEXT:         %[[v30:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v31:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:         %[[v32:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 9 : i32}> : () -> i32
// CHECK-NEXT:         %[[v33:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
// CHECK-NEXT:         %[[v34:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// CHECK-NEXT:         %[[v35:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 14 : i32}> : () -> i32
// CHECK-NEXT:         %[[v36:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
// CHECK-NEXT:         %[[v37:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:         %[[v38:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
// CHECK-NEXT:         %[[v39:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
// CHECK-NEXT:         %[[v40:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 13 : i64}> : () -> i64
// CHECK-NEXT:         %[[v41:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v8]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v9]], %[[v41]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v43:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v10]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v11]], %[[v43]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v45:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v12]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v13]], %[[v45]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v47:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v14]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v15]], %[[v47]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb49:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb49]](%[[varg49_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v51:[0-9]+]] = "llvm.icmp"(%[[varg49_0]], %[[v16]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v51]]) [^[[bb52:[0-9]+]], ^[[bb53:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb52]]():
// CHECK-NEXT:         %[[v55:[0-9]+]] = "llvm.mul"(%[[v20]], %[[varg49_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v56:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v55]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v57:[0-9]+]] = "llvm.load"(%[[v56]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v58:[0-9]+]] = "llvm.zext"(%[[v57]]) : (i8) -> i32
// CHECK-NEXT:         %[[v59:[0-9]+]] = "llvm.getelementptr"(%[[v56]], %[[v10]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v60:[0-9]+]] = "llvm.load"(%[[v59]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v61:[0-9]+]] = "llvm.zext"(%[[v60]]) : (i8) -> i32
// CHECK-NEXT:         %[[v62:[0-9]+]] = "llvm.shl"(%[[v61]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v63:[0-9]+]] = "llvm.or"(%[[v58]], %[[v62]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v64:[0-9]+]] = "llvm.getelementptr"(%[[v56]], %[[v12]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v65:[0-9]+]] = "llvm.load"(%[[v64]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v66:[0-9]+]] = "llvm.zext"(%[[v65]]) : (i8) -> i32
// CHECK-NEXT:         %[[v67:[0-9]+]] = "llvm.shl"(%[[v66]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v68:[0-9]+]] = "llvm.or"(%[[v63]], %[[v67]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v69:[0-9]+]] = "llvm.getelementptr"(%[[v56]], %[[v14]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v70:[0-9]+]] = "llvm.load"(%[[v69]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v71:[0-9]+]] = "llvm.zext"(%[[v70]]) : (i8) -> i32
// CHECK-NEXT:         %[[v72:[0-9]+]] = "llvm.shl"(%[[v71]], %[[v23]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v73:[0-9]+]] = "llvm.or"(%[[v68]], %[[v72]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v74:[0-9]+]] = "llvm.add"(%[[v20]], %[[varg49_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v75:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v74]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v73]], %[[v75]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb77:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb77]]():
// CHECK-NEXT:         %[[v79:[0-9]+]] = "llvm.add"(%[[varg49_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v79]]) [^[[bb49]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb53]]():
// CHECK-NEXT:         %[[v81:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v17]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[varg7_1]], %[[v81]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb83:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb83]](%[[varg83_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v85:[0-9]+]] = "llvm.icmp"(%[[varg83_0]], %[[v14]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v85]]) [^[[bb86:[0-9]+]], ^[[bb87:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb86]]():
// CHECK-NEXT:         %[[v89:[0-9]+]] = "llvm.mul"(%[[v20]], %[[varg83_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v90:[0-9]+]] = "llvm.getelementptr"(%[[varg7_2]], %[[v89]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v91:[0-9]+]] = "llvm.load"(%[[v90]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v92:[0-9]+]] = "llvm.zext"(%[[v91]]) : (i8) -> i32
// CHECK-NEXT:         %[[v93:[0-9]+]] = "llvm.getelementptr"(%[[v90]], %[[v10]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v94:[0-9]+]] = "llvm.load"(%[[v93]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v95:[0-9]+]] = "llvm.zext"(%[[v94]]) : (i8) -> i32
// CHECK-NEXT:         %[[v96:[0-9]+]] = "llvm.shl"(%[[v95]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v97:[0-9]+]] = "llvm.or"(%[[v92]], %[[v96]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v98:[0-9]+]] = "llvm.getelementptr"(%[[v90]], %[[v12]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v99:[0-9]+]] = "llvm.load"(%[[v98]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v100:[0-9]+]] = "llvm.zext"(%[[v99]]) : (i8) -> i32
// CHECK-NEXT:         %[[v101:[0-9]+]] = "llvm.shl"(%[[v100]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v102:[0-9]+]] = "llvm.or"(%[[v97]], %[[v101]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v103:[0-9]+]] = "llvm.getelementptr"(%[[v90]], %[[v14]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v104:[0-9]+]] = "llvm.load"(%[[v103]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v105:[0-9]+]] = "llvm.zext"(%[[v104]]) : (i8) -> i32
// CHECK-NEXT:         %[[v106:[0-9]+]] = "llvm.shl"(%[[v105]], %[[v23]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v107:[0-9]+]] = "llvm.or"(%[[v102]], %[[v106]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v108:[0-9]+]] = "llvm.add"(%[[v40]], %[[varg83_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v109:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v108]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v107]], %[[v109]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb111:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb111]]():
// CHECK-NEXT:         %[[v113:[0-9]+]] = "llvm.add"(%[[varg83_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v113]]) [^[[bb83]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb87]]():
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb115:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb115]](%[[varg115_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v117:[0-9]+]] = "llvm.icmp"(%[[varg115_0]], %[[v18]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v117]]) [^[[bb118:[0-9]+]], ^[[bb119:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb118]]():
// CHECK-NEXT:         %[[v121:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[varg115_0]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v122:[0-9]+]] = "llvm.load"(%[[v121]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v123:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[varg115_0]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v122]], %[[v123]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb125:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb125]]():
// CHECK-NEXT:         %[[v127:[0-9]+]] = "llvm.add"(%[[varg115_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v127]]) [^[[bb115]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb119]]():
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb129:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb129]](%[[varg129_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v131:[0-9]+]] = "llvm.icmp"(%[[varg129_0]], %[[v19]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v131]]) [^[[bb132:[0-9]+]], ^[[bb133:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb132]]():
// CHECK-NEXT:         %[[v135:[0-9]+]] = "llvm.sext"(%[[v24]]) : (i32) -> i64
// CHECK-NEXT:         %[[v136:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v137:[0-9]+]] = "llvm.load"(%[[v136]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v138:[0-9]+]] = "llvm.sext"(%[[v25]]) : (i32) -> i64
// CHECK-NEXT:         %[[v139:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v140:[0-9]+]] = "llvm.load"(%[[v139]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v141:[0-9]+]] = "llvm.add"(%[[v140]], %[[v137]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v141]], %[[v139]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v144:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v145:[0-9]+]] = "llvm.load"(%[[v144]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v146:[0-9]+]] = "llvm.sext"(%[[v26]]) : (i32) -> i64
// CHECK-NEXT:         %[[v147:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v148:[0-9]+]] = "llvm.load"(%[[v147]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v149:[0-9]+]] = "llvm.xor"(%[[v148]], %[[v145]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v149]], %[[v147]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v152:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v153:[0-9]+]] = "llvm.load"(%[[v152]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v154:[0-9]+]] = "llvm.shl"(%[[v153]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v155:[0-9]+]] = "llvm.sub"(%[[v27]], %[[v22]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v156:[0-9]+]] = "llvm.lshr"(%[[v153]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v157:[0-9]+]] = "llvm.or"(%[[v154]], %[[v156]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v159:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v157]], %[[v159]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v162:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v163:[0-9]+]] = "llvm.load"(%[[v162]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v164:[0-9]+]] = "llvm.sext"(%[[v21]]) : (i32) -> i64
// CHECK-NEXT:         %[[v165:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v164]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v166:[0-9]+]] = "llvm.load"(%[[v165]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v167:[0-9]+]] = "llvm.add"(%[[v166]], %[[v163]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v167]], %[[v165]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v170:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v164]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v171:[0-9]+]] = "llvm.load"(%[[v170]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v173:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v174:[0-9]+]] = "llvm.load"(%[[v173]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v175:[0-9]+]] = "llvm.xor"(%[[v174]], %[[v171]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v175]], %[[v173]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v178:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v179:[0-9]+]] = "llvm.load"(%[[v178]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v180:[0-9]+]] = "llvm.shl"(%[[v179]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v181:[0-9]+]] = "llvm.sub"(%[[v27]], %[[v26]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v182:[0-9]+]] = "llvm.lshr"(%[[v179]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v183:[0-9]+]] = "llvm.or"(%[[v180]], %[[v182]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v185:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v183]], %[[v185]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v188:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v189:[0-9]+]] = "llvm.load"(%[[v188]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v191:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v192:[0-9]+]] = "llvm.load"(%[[v191]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v193:[0-9]+]] = "llvm.add"(%[[v192]], %[[v189]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v193]], %[[v191]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v196:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v197:[0-9]+]] = "llvm.load"(%[[v196]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v199:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v200:[0-9]+]] = "llvm.load"(%[[v199]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v201:[0-9]+]] = "llvm.xor"(%[[v200]], %[[v197]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v201]], %[[v199]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v204:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v205:[0-9]+]] = "llvm.load"(%[[v204]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v206:[0-9]+]] = "llvm.shl"(%[[v205]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v207:[0-9]+]] = "llvm.sub"(%[[v27]], %[[v21]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v208:[0-9]+]] = "llvm.lshr"(%[[v205]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v209:[0-9]+]] = "llvm.or"(%[[v206]], %[[v208]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v211:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v209]], %[[v211]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v214:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v215:[0-9]+]] = "llvm.load"(%[[v214]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v217:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v164]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v218:[0-9]+]] = "llvm.load"(%[[v217]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v219:[0-9]+]] = "llvm.add"(%[[v218]], %[[v215]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v219]], %[[v217]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v222:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v164]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v223:[0-9]+]] = "llvm.load"(%[[v222]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v225:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v226:[0-9]+]] = "llvm.load"(%[[v225]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v227:[0-9]+]] = "llvm.xor"(%[[v226]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v227]], %[[v225]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v230:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v231:[0-9]+]] = "llvm.load"(%[[v230]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v232:[0-9]+]] = "llvm.shl"(%[[v231]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v233:[0-9]+]] = "llvm.sub"(%[[v27]], %[[v28]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v234:[0-9]+]] = "llvm.lshr"(%[[v231]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v235:[0-9]+]] = "llvm.or"(%[[v232]], %[[v234]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v237:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v235]], %[[v237]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v239:[0-9]+]] = "llvm.sext"(%[[v29]]) : (i32) -> i64
// CHECK-NEXT:         %[[v240:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v241:[0-9]+]] = "llvm.load"(%[[v240]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v242:[0-9]+]] = "llvm.sext"(%[[v30]]) : (i32) -> i64
// CHECK-NEXT:         %[[v243:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v242]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v244:[0-9]+]] = "llvm.load"(%[[v243]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v245:[0-9]+]] = "llvm.add"(%[[v244]], %[[v241]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v245]], %[[v243]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v248:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v242]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v249:[0-9]+]] = "llvm.load"(%[[v248]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v250:[0-9]+]] = "llvm.sext"(%[[v31]]) : (i32) -> i64
// CHECK-NEXT:         %[[v251:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v252:[0-9]+]] = "llvm.load"(%[[v251]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v253:[0-9]+]] = "llvm.xor"(%[[v252]], %[[v249]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v253]], %[[v251]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v256:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v257:[0-9]+]] = "llvm.load"(%[[v256]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v258:[0-9]+]] = "llvm.shl"(%[[v257]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v260:[0-9]+]] = "llvm.lshr"(%[[v257]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v261:[0-9]+]] = "llvm.or"(%[[v258]], %[[v260]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v263:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v261]], %[[v263]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v266:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v267:[0-9]+]] = "llvm.load"(%[[v266]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v268:[0-9]+]] = "llvm.sext"(%[[v32]]) : (i32) -> i64
// CHECK-NEXT:         %[[v269:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v268]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v270:[0-9]+]] = "llvm.load"(%[[v269]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v271:[0-9]+]] = "llvm.add"(%[[v270]], %[[v267]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v271]], %[[v269]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v274:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v268]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v275:[0-9]+]] = "llvm.load"(%[[v274]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v277:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v278:[0-9]+]] = "llvm.load"(%[[v277]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v279:[0-9]+]] = "llvm.xor"(%[[v278]], %[[v275]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v279]], %[[v277]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v282:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v283:[0-9]+]] = "llvm.load"(%[[v282]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v284:[0-9]+]] = "llvm.shl"(%[[v283]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v286:[0-9]+]] = "llvm.lshr"(%[[v283]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v287:[0-9]+]] = "llvm.or"(%[[v284]], %[[v286]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v289:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v287]], %[[v289]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v292:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v293:[0-9]+]] = "llvm.load"(%[[v292]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v295:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v242]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v296:[0-9]+]] = "llvm.load"(%[[v295]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v297:[0-9]+]] = "llvm.add"(%[[v296]], %[[v293]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v297]], %[[v295]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v300:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v242]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v301:[0-9]+]] = "llvm.load"(%[[v300]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v303:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v304:[0-9]+]] = "llvm.load"(%[[v303]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v305:[0-9]+]] = "llvm.xor"(%[[v304]], %[[v301]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v305]], %[[v303]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v308:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v309:[0-9]+]] = "llvm.load"(%[[v308]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v310:[0-9]+]] = "llvm.shl"(%[[v309]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v312:[0-9]+]] = "llvm.lshr"(%[[v309]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v313:[0-9]+]] = "llvm.or"(%[[v310]], %[[v312]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v315:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v313]], %[[v315]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v318:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v319:[0-9]+]] = "llvm.load"(%[[v318]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v321:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v268]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v322:[0-9]+]] = "llvm.load"(%[[v321]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v323:[0-9]+]] = "llvm.add"(%[[v322]], %[[v319]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v323]], %[[v321]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v326:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v268]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v327:[0-9]+]] = "llvm.load"(%[[v326]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v329:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v330:[0-9]+]] = "llvm.load"(%[[v329]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v331:[0-9]+]] = "llvm.xor"(%[[v330]], %[[v327]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v331]], %[[v329]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v334:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v335:[0-9]+]] = "llvm.load"(%[[v334]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v336:[0-9]+]] = "llvm.shl"(%[[v335]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v338:[0-9]+]] = "llvm.lshr"(%[[v335]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v339:[0-9]+]] = "llvm.or"(%[[v336]], %[[v338]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v341:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v339]], %[[v341]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v343:[0-9]+]] = "llvm.sext"(%[[v33]]) : (i32) -> i64
// CHECK-NEXT:         %[[v344:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v345:[0-9]+]] = "llvm.load"(%[[v344]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v346:[0-9]+]] = "llvm.sext"(%[[v34]]) : (i32) -> i64
// CHECK-NEXT:         %[[v347:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v346]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v348:[0-9]+]] = "llvm.load"(%[[v347]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v349:[0-9]+]] = "llvm.add"(%[[v348]], %[[v345]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v349]], %[[v347]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v352:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v346]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v353:[0-9]+]] = "llvm.load"(%[[v352]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v354:[0-9]+]] = "llvm.sext"(%[[v35]]) : (i32) -> i64
// CHECK-NEXT:         %[[v355:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v356:[0-9]+]] = "llvm.load"(%[[v355]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v357:[0-9]+]] = "llvm.xor"(%[[v356]], %[[v353]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v357]], %[[v355]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v360:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v361:[0-9]+]] = "llvm.load"(%[[v360]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v362:[0-9]+]] = "llvm.shl"(%[[v361]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v364:[0-9]+]] = "llvm.lshr"(%[[v361]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v365:[0-9]+]] = "llvm.or"(%[[v362]], %[[v364]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v367:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v365]], %[[v367]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v370:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v371:[0-9]+]] = "llvm.load"(%[[v370]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v372:[0-9]+]] = "llvm.sext"(%[[v36]]) : (i32) -> i64
// CHECK-NEXT:         %[[v373:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v372]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v374:[0-9]+]] = "llvm.load"(%[[v373]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v375:[0-9]+]] = "llvm.add"(%[[v374]], %[[v371]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v375]], %[[v373]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v378:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v372]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v379:[0-9]+]] = "llvm.load"(%[[v378]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v381:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v382:[0-9]+]] = "llvm.load"(%[[v381]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v383:[0-9]+]] = "llvm.xor"(%[[v382]], %[[v379]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v383]], %[[v381]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v386:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v387:[0-9]+]] = "llvm.load"(%[[v386]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v388:[0-9]+]] = "llvm.shl"(%[[v387]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v390:[0-9]+]] = "llvm.lshr"(%[[v387]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v391:[0-9]+]] = "llvm.or"(%[[v388]], %[[v390]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v393:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v391]], %[[v393]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v396:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v397:[0-9]+]] = "llvm.load"(%[[v396]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v399:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v346]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v400:[0-9]+]] = "llvm.load"(%[[v399]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v401:[0-9]+]] = "llvm.add"(%[[v400]], %[[v397]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v401]], %[[v399]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v404:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v346]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v405:[0-9]+]] = "llvm.load"(%[[v404]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v407:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v408:[0-9]+]] = "llvm.load"(%[[v407]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v409:[0-9]+]] = "llvm.xor"(%[[v408]], %[[v405]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v409]], %[[v407]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v412:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v413:[0-9]+]] = "llvm.load"(%[[v412]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v414:[0-9]+]] = "llvm.shl"(%[[v413]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v416:[0-9]+]] = "llvm.lshr"(%[[v413]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v417:[0-9]+]] = "llvm.or"(%[[v414]], %[[v416]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v419:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v417]], %[[v419]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v422:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v423:[0-9]+]] = "llvm.load"(%[[v422]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v425:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v372]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v426:[0-9]+]] = "llvm.load"(%[[v425]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v427:[0-9]+]] = "llvm.add"(%[[v426]], %[[v423]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v427]], %[[v425]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v430:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v372]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v431:[0-9]+]] = "llvm.load"(%[[v430]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v433:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v434:[0-9]+]] = "llvm.load"(%[[v433]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v435:[0-9]+]] = "llvm.xor"(%[[v434]], %[[v431]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v435]], %[[v433]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v438:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v439:[0-9]+]] = "llvm.load"(%[[v438]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v440:[0-9]+]] = "llvm.shl"(%[[v439]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v442:[0-9]+]] = "llvm.lshr"(%[[v439]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v443:[0-9]+]] = "llvm.or"(%[[v440]], %[[v442]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v445:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v443]], %[[v445]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v447:[0-9]+]] = "llvm.sext"(%[[v28]]) : (i32) -> i64
// CHECK-NEXT:         %[[v448:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v449:[0-9]+]] = "llvm.load"(%[[v448]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v450:[0-9]+]] = "llvm.sext"(%[[v37]]) : (i32) -> i64
// CHECK-NEXT:         %[[v451:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v450]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v452:[0-9]+]] = "llvm.load"(%[[v451]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v453:[0-9]+]] = "llvm.add"(%[[v452]], %[[v449]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v453]], %[[v451]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v456:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v450]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v457:[0-9]+]] = "llvm.load"(%[[v456]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v458:[0-9]+]] = "llvm.sext"(%[[v38]]) : (i32) -> i64
// CHECK-NEXT:         %[[v459:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v460:[0-9]+]] = "llvm.load"(%[[v459]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v461:[0-9]+]] = "llvm.xor"(%[[v460]], %[[v457]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v461]], %[[v459]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v464:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v465:[0-9]+]] = "llvm.load"(%[[v464]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v466:[0-9]+]] = "llvm.shl"(%[[v465]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v468:[0-9]+]] = "llvm.lshr"(%[[v465]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v469:[0-9]+]] = "llvm.or"(%[[v466]], %[[v468]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v471:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v469]], %[[v471]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v474:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v475:[0-9]+]] = "llvm.load"(%[[v474]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v476:[0-9]+]] = "llvm.sext"(%[[v39]]) : (i32) -> i64
// CHECK-NEXT:         %[[v477:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v476]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v478:[0-9]+]] = "llvm.load"(%[[v477]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v479:[0-9]+]] = "llvm.add"(%[[v478]], %[[v475]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v479]], %[[v477]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v482:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v476]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v483:[0-9]+]] = "llvm.load"(%[[v482]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v485:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v486:[0-9]+]] = "llvm.load"(%[[v485]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v487:[0-9]+]] = "llvm.xor"(%[[v486]], %[[v483]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v487]], %[[v485]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v490:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v491:[0-9]+]] = "llvm.load"(%[[v490]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v492:[0-9]+]] = "llvm.shl"(%[[v491]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v494:[0-9]+]] = "llvm.lshr"(%[[v491]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v495:[0-9]+]] = "llvm.or"(%[[v492]], %[[v494]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v497:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v495]], %[[v497]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v500:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v501:[0-9]+]] = "llvm.load"(%[[v500]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v503:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v450]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v504:[0-9]+]] = "llvm.load"(%[[v503]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v505:[0-9]+]] = "llvm.add"(%[[v504]], %[[v501]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v505]], %[[v503]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v508:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v450]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v509:[0-9]+]] = "llvm.load"(%[[v508]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v511:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v512:[0-9]+]] = "llvm.load"(%[[v511]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v513:[0-9]+]] = "llvm.xor"(%[[v512]], %[[v509]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v513]], %[[v511]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v516:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v517:[0-9]+]] = "llvm.load"(%[[v516]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v518:[0-9]+]] = "llvm.shl"(%[[v517]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v520:[0-9]+]] = "llvm.lshr"(%[[v517]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v521:[0-9]+]] = "llvm.or"(%[[v518]], %[[v520]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v523:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v521]], %[[v523]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v526:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v527:[0-9]+]] = "llvm.load"(%[[v526]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v529:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v476]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v530:[0-9]+]] = "llvm.load"(%[[v529]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v531:[0-9]+]] = "llvm.add"(%[[v530]], %[[v527]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v531]], %[[v529]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v534:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v476]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v535:[0-9]+]] = "llvm.load"(%[[v534]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v537:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v538:[0-9]+]] = "llvm.load"(%[[v537]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v539:[0-9]+]] = "llvm.xor"(%[[v538]], %[[v535]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v539]], %[[v537]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v542:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v543:[0-9]+]] = "llvm.load"(%[[v542]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v544:[0-9]+]] = "llvm.shl"(%[[v543]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v546:[0-9]+]] = "llvm.lshr"(%[[v543]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v547:[0-9]+]] = "llvm.or"(%[[v544]], %[[v546]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v549:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v547]], %[[v549]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v552:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v553:[0-9]+]] = "llvm.load"(%[[v552]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v555:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v556:[0-9]+]] = "llvm.load"(%[[v555]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v557:[0-9]+]] = "llvm.add"(%[[v556]], %[[v553]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v557]], %[[v555]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v560:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v561:[0-9]+]] = "llvm.load"(%[[v560]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v563:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v564:[0-9]+]] = "llvm.load"(%[[v563]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v565:[0-9]+]] = "llvm.xor"(%[[v564]], %[[v561]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v565]], %[[v563]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v568:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v569:[0-9]+]] = "llvm.load"(%[[v568]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v570:[0-9]+]] = "llvm.shl"(%[[v569]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v572:[0-9]+]] = "llvm.lshr"(%[[v569]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v573:[0-9]+]] = "llvm.or"(%[[v570]], %[[v572]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v575:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v573]], %[[v575]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v578:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v579:[0-9]+]] = "llvm.load"(%[[v578]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v581:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v372]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v582:[0-9]+]] = "llvm.load"(%[[v581]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v583:[0-9]+]] = "llvm.add"(%[[v582]], %[[v579]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v583]], %[[v581]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v586:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v372]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v587:[0-9]+]] = "llvm.load"(%[[v586]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v589:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v590:[0-9]+]] = "llvm.load"(%[[v589]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v591:[0-9]+]] = "llvm.xor"(%[[v590]], %[[v587]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v591]], %[[v589]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v594:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v595:[0-9]+]] = "llvm.load"(%[[v594]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v596:[0-9]+]] = "llvm.shl"(%[[v595]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v598:[0-9]+]] = "llvm.lshr"(%[[v595]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v599:[0-9]+]] = "llvm.or"(%[[v596]], %[[v598]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v601:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v599]], %[[v601]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v604:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v605:[0-9]+]] = "llvm.load"(%[[v604]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v607:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v608:[0-9]+]] = "llvm.load"(%[[v607]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v609:[0-9]+]] = "llvm.add"(%[[v608]], %[[v605]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v609]], %[[v607]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v612:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v613:[0-9]+]] = "llvm.load"(%[[v612]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v615:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v616:[0-9]+]] = "llvm.load"(%[[v615]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v617:[0-9]+]] = "llvm.xor"(%[[v616]], %[[v613]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v617]], %[[v615]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v620:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v621:[0-9]+]] = "llvm.load"(%[[v620]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v622:[0-9]+]] = "llvm.shl"(%[[v621]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v624:[0-9]+]] = "llvm.lshr"(%[[v621]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v625:[0-9]+]] = "llvm.or"(%[[v622]], %[[v624]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v627:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v625]], %[[v627]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v630:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v458]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v631:[0-9]+]] = "llvm.load"(%[[v630]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v633:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v372]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v634:[0-9]+]] = "llvm.load"(%[[v633]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v635:[0-9]+]] = "llvm.add"(%[[v634]], %[[v631]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v635]], %[[v633]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v638:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v372]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v639:[0-9]+]] = "llvm.load"(%[[v638]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v641:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v642:[0-9]+]] = "llvm.load"(%[[v641]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v643:[0-9]+]] = "llvm.xor"(%[[v642]], %[[v639]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v643]], %[[v641]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v646:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v647:[0-9]+]] = "llvm.load"(%[[v646]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v648:[0-9]+]] = "llvm.shl"(%[[v647]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v650:[0-9]+]] = "llvm.lshr"(%[[v647]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v651:[0-9]+]] = "llvm.or"(%[[v648]], %[[v650]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v653:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v239]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v651]], %[[v653]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v656:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v657:[0-9]+]] = "llvm.load"(%[[v656]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v659:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v242]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v660:[0-9]+]] = "llvm.load"(%[[v659]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v661:[0-9]+]] = "llvm.add"(%[[v660]], %[[v657]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v661]], %[[v659]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v664:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v242]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v665:[0-9]+]] = "llvm.load"(%[[v664]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v667:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v668:[0-9]+]] = "llvm.load"(%[[v667]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v669:[0-9]+]] = "llvm.xor"(%[[v668]], %[[v665]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v669]], %[[v667]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v672:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v673:[0-9]+]] = "llvm.load"(%[[v672]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v674:[0-9]+]] = "llvm.shl"(%[[v673]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v676:[0-9]+]] = "llvm.lshr"(%[[v673]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v677:[0-9]+]] = "llvm.or"(%[[v674]], %[[v676]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v679:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v677]], %[[v679]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v682:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v683:[0-9]+]] = "llvm.load"(%[[v682]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v685:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v476]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v686:[0-9]+]] = "llvm.load"(%[[v685]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v687:[0-9]+]] = "llvm.add"(%[[v686]], %[[v683]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v687]], %[[v685]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v690:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v476]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v691:[0-9]+]] = "llvm.load"(%[[v690]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v693:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v694:[0-9]+]] = "llvm.load"(%[[v693]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v695:[0-9]+]] = "llvm.xor"(%[[v694]], %[[v691]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v695]], %[[v693]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v698:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v699:[0-9]+]] = "llvm.load"(%[[v698]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v700:[0-9]+]] = "llvm.shl"(%[[v699]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v702:[0-9]+]] = "llvm.lshr"(%[[v699]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v703:[0-9]+]] = "llvm.or"(%[[v700]], %[[v702]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v705:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v703]], %[[v705]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v708:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v709:[0-9]+]] = "llvm.load"(%[[v708]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v711:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v242]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v712:[0-9]+]] = "llvm.load"(%[[v711]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v713:[0-9]+]] = "llvm.add"(%[[v712]], %[[v709]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v713]], %[[v711]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v716:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v242]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v717:[0-9]+]] = "llvm.load"(%[[v716]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v719:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v720:[0-9]+]] = "llvm.load"(%[[v719]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v721:[0-9]+]] = "llvm.xor"(%[[v720]], %[[v717]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v721]], %[[v719]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v724:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v725:[0-9]+]] = "llvm.load"(%[[v724]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v726:[0-9]+]] = "llvm.shl"(%[[v725]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v728:[0-9]+]] = "llvm.lshr"(%[[v725]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v729:[0-9]+]] = "llvm.or"(%[[v726]], %[[v728]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v731:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v729]], %[[v731]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v734:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v146]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v735:[0-9]+]] = "llvm.load"(%[[v734]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v737:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v476]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v738:[0-9]+]] = "llvm.load"(%[[v737]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v739:[0-9]+]] = "llvm.add"(%[[v738]], %[[v735]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v739]], %[[v737]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v742:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v476]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v743:[0-9]+]] = "llvm.load"(%[[v742]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v745:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v746:[0-9]+]] = "llvm.load"(%[[v745]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v747:[0-9]+]] = "llvm.xor"(%[[v746]], %[[v743]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v747]], %[[v745]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v750:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v751:[0-9]+]] = "llvm.load"(%[[v750]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v752:[0-9]+]] = "llvm.shl"(%[[v751]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v754:[0-9]+]] = "llvm.lshr"(%[[v751]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v755:[0-9]+]] = "llvm.or"(%[[v752]], %[[v754]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v757:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v343]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v755]], %[[v757]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v760:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v761:[0-9]+]] = "llvm.load"(%[[v760]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v763:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v346]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v764:[0-9]+]] = "llvm.load"(%[[v763]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v765:[0-9]+]] = "llvm.add"(%[[v764]], %[[v761]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v765]], %[[v763]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v768:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v346]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v769:[0-9]+]] = "llvm.load"(%[[v768]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v771:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v772:[0-9]+]] = "llvm.load"(%[[v771]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v773:[0-9]+]] = "llvm.xor"(%[[v772]], %[[v769]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v773]], %[[v771]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v776:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v777:[0-9]+]] = "llvm.load"(%[[v776]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v778:[0-9]+]] = "llvm.shl"(%[[v777]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v780:[0-9]+]] = "llvm.lshr"(%[[v777]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v781:[0-9]+]] = "llvm.or"(%[[v778]], %[[v780]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v783:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v781]], %[[v783]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v786:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v787:[0-9]+]] = "llvm.load"(%[[v786]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v789:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v164]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v790:[0-9]+]] = "llvm.load"(%[[v789]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v791:[0-9]+]] = "llvm.add"(%[[v790]], %[[v787]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v791]], %[[v789]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v794:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v164]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v795:[0-9]+]] = "llvm.load"(%[[v794]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v797:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v798:[0-9]+]] = "llvm.load"(%[[v797]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v799:[0-9]+]] = "llvm.xor"(%[[v798]], %[[v795]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v799]], %[[v797]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v802:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v803:[0-9]+]] = "llvm.load"(%[[v802]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v804:[0-9]+]] = "llvm.shl"(%[[v803]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v806:[0-9]+]] = "llvm.lshr"(%[[v803]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v807:[0-9]+]] = "llvm.or"(%[[v804]], %[[v806]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v809:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v807]], %[[v809]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v812:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v813:[0-9]+]] = "llvm.load"(%[[v812]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v815:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v346]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v816:[0-9]+]] = "llvm.load"(%[[v815]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v817:[0-9]+]] = "llvm.add"(%[[v816]], %[[v813]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v817]], %[[v815]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v820:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v346]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v821:[0-9]+]] = "llvm.load"(%[[v820]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v823:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v824:[0-9]+]] = "llvm.load"(%[[v823]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v825:[0-9]+]] = "llvm.xor"(%[[v824]], %[[v821]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v825]], %[[v823]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v828:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v829:[0-9]+]] = "llvm.load"(%[[v828]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v830:[0-9]+]] = "llvm.shl"(%[[v829]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v832:[0-9]+]] = "llvm.lshr"(%[[v829]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v833:[0-9]+]] = "llvm.or"(%[[v830]], %[[v832]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v835:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v833]], %[[v835]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v838:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v250]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v839:[0-9]+]] = "llvm.load"(%[[v838]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v841:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v164]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v842:[0-9]+]] = "llvm.load"(%[[v841]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v843:[0-9]+]] = "llvm.add"(%[[v842]], %[[v839]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v843]], %[[v841]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v846:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v164]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v847:[0-9]+]] = "llvm.load"(%[[v846]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v849:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v850:[0-9]+]] = "llvm.load"(%[[v849]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v851:[0-9]+]] = "llvm.xor"(%[[v850]], %[[v847]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v851]], %[[v849]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v854:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v855:[0-9]+]] = "llvm.load"(%[[v854]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v856:[0-9]+]] = "llvm.shl"(%[[v855]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v858:[0-9]+]] = "llvm.lshr"(%[[v855]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v859:[0-9]+]] = "llvm.or"(%[[v856]], %[[v858]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v861:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v447]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v859]], %[[v861]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v864:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v865:[0-9]+]] = "llvm.load"(%[[v864]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v867:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v450]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v868:[0-9]+]] = "llvm.load"(%[[v867]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v869:[0-9]+]] = "llvm.add"(%[[v868]], %[[v865]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v869]], %[[v867]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v872:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v450]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v873:[0-9]+]] = "llvm.load"(%[[v872]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v875:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v876:[0-9]+]] = "llvm.load"(%[[v875]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v877:[0-9]+]] = "llvm.xor"(%[[v876]], %[[v873]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v877]], %[[v875]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v880:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v881:[0-9]+]] = "llvm.load"(%[[v880]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v882:[0-9]+]] = "llvm.shl"(%[[v881]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v884:[0-9]+]] = "llvm.lshr"(%[[v881]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v885:[0-9]+]] = "llvm.or"(%[[v882]], %[[v884]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v887:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v885]], %[[v887]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v890:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v891:[0-9]+]] = "llvm.load"(%[[v890]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v893:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v268]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v894:[0-9]+]] = "llvm.load"(%[[v893]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v895:[0-9]+]] = "llvm.add"(%[[v894]], %[[v891]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v895]], %[[v893]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v898:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v268]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v899:[0-9]+]] = "llvm.load"(%[[v898]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v901:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v902:[0-9]+]] = "llvm.load"(%[[v901]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v903:[0-9]+]] = "llvm.xor"(%[[v902]], %[[v899]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v903]], %[[v901]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v906:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v907:[0-9]+]] = "llvm.load"(%[[v906]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v908:[0-9]+]] = "llvm.shl"(%[[v907]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v910:[0-9]+]] = "llvm.lshr"(%[[v907]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v911:[0-9]+]] = "llvm.or"(%[[v908]], %[[v910]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v913:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v911]], %[[v913]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v916:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v917:[0-9]+]] = "llvm.load"(%[[v916]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v919:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v450]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v920:[0-9]+]] = "llvm.load"(%[[v919]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v921:[0-9]+]] = "llvm.add"(%[[v920]], %[[v917]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v921]], %[[v919]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v924:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v450]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v925:[0-9]+]] = "llvm.load"(%[[v924]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v927:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v928:[0-9]+]] = "llvm.load"(%[[v927]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v929:[0-9]+]] = "llvm.xor"(%[[v928]], %[[v925]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v929]], %[[v927]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v932:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v933:[0-9]+]] = "llvm.load"(%[[v932]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v934:[0-9]+]] = "llvm.shl"(%[[v933]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v936:[0-9]+]] = "llvm.lshr"(%[[v933]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v937:[0-9]+]] = "llvm.or"(%[[v934]], %[[v936]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v939:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v937]], %[[v939]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v942:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v354]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v943:[0-9]+]] = "llvm.load"(%[[v942]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v945:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v268]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v946:[0-9]+]] = "llvm.load"(%[[v945]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v947:[0-9]+]] = "llvm.add"(%[[v946]], %[[v943]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v947]], %[[v945]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v950:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v268]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v951:[0-9]+]] = "llvm.load"(%[[v950]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v953:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v954:[0-9]+]] = "llvm.load"(%[[v953]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v955:[0-9]+]] = "llvm.xor"(%[[v954]], %[[v951]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v955]], %[[v953]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v958:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v959:[0-9]+]] = "llvm.load"(%[[v958]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v960:[0-9]+]] = "llvm.shl"(%[[v959]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v962:[0-9]+]] = "llvm.lshr"(%[[v959]], %[[v233]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v963:[0-9]+]] = "llvm.or"(%[[v960]], %[[v962]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v965:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v963]], %[[v965]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb967:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb967]]():
// CHECK-NEXT:         %[[v969:[0-9]+]] = "llvm.add"(%[[varg129_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v969]]) [^[[bb129]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb133]]():
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb971:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb971]](%[[varg971_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v973:[0-9]+]] = "llvm.icmp"(%[[varg971_0]], %[[v18]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v973]]) [^[[bb974:[0-9]+]], ^[[bb975:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb974]]():
// CHECK-NEXT:         %[[v977:[0-9]+]] = "llvm.mul"(%[[v20]], %[[varg971_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v978:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v977]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v979:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[varg971_0]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v980:[0-9]+]] = "llvm.load"(%[[v979]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v981:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[varg971_0]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v982:[0-9]+]] = "llvm.load"(%[[v981]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v983:[0-9]+]] = "llvm.add"(%[[v980]], %[[v982]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v984:[0-9]+]] = "llvm.trunc"(%[[v983]]) : (i32) -> i8
// CHECK-NEXT:         "llvm.store"(%[[v984]], %[[v978]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v986:[0-9]+]] = "llvm.lshr"(%[[v983]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v987:[0-9]+]] = "llvm.trunc"(%[[v986]]) : (i32) -> i8
// CHECK-NEXT:         %[[v988:[0-9]+]] = "llvm.getelementptr"(%[[v978]], %[[v10]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v987]], %[[v988]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v990:[0-9]+]] = "llvm.lshr"(%[[v983]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v991:[0-9]+]] = "llvm.trunc"(%[[v990]]) : (i32) -> i8
// CHECK-NEXT:         %[[v992:[0-9]+]] = "llvm.getelementptr"(%[[v978]], %[[v12]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v991]], %[[v992]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v994:[0-9]+]] = "llvm.lshr"(%[[v983]], %[[v23]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v995:[0-9]+]] = "llvm.trunc"(%[[v994]]) : (i32) -> i8
// CHECK-NEXT:         %[[v996:[0-9]+]] = "llvm.getelementptr"(%[[v978]], %[[v14]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v995]], %[[v996]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb998:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb998]]():
// CHECK-NEXT:         %[[v1000:[0-9]+]] = "llvm.add"(%[[varg971_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v1000]]) [^[[bb971]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb975]]():
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()
