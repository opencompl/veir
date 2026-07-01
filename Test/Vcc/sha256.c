// RUN: ./Tools/vcc -O --emit-mlir %s -o - | filecheck %s
// RUN: ./Tools/vcc -c %s -o %t.o
// RUN: test -s %t.o
// RUN: ./Tools/vcc -S %s -o %t.s
// RUN: test -s %t.s
/*
    SHA-256 block compression function (FIPS 180-4), processing one 512-bit block.

    Like fastntt.c / chacha20.c, this is a single exported function operating on
    caller-provided buffers, with no local arrays and no globals:
      - H: 8 state words   (read + updated in place)
      - M: 16 message words (the input block)
      - K: 64 round constants
      - W: 64-word scratch  (the message schedule)

    The block compression function is the core part of the SHA-256 hash function, which hashes 
    an arbitrary message by padding it to a multiple of 512 bits and iterating this compression function
    over each 512-bit block. The compression function is the "core" of the hash.

    Some references for the SHA-256 compression function & the algorithm in general:
      - FIPS 180-4: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
      - RFC 6234: https://datatracker.ietf.org/doc/html/rfc6234

*/
#include <stdint.h>

// right-rotate a 32-bit word
__attribute__((always_inline)) static uint32_t rotr(uint32_t x, int n) {
    return (x >> n) | (x << (32 - n));}

// message schedule   
__attribute__((always_inline)) void sha256_block(uint32_t *H, const uint32_t *M, const uint32_t *K, uint32_t *W) {
    for (int i = 0; i < 16; i++)
        W[i] = M[i];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr(W[i-15], 7) ^ rotr(W[i-15], 18) ^ (W[i-15] >> 3);
        uint32_t s1 = rotr(W[i-2], 17) ^ rotr(W[i-2], 19) ^ (W[i-2] >> 10);
        W[i] = W[i-16] + s0 + W[i-7] + s1;
    }

    // compression
    uint32_t a=H[0];
    uint32_t b=H[1];
    uint32_t c=H[2];
    uint32_t d=H[3];
    uint32_t e=H[4];
    uint32_t f=H[5];
    uint32_t g=H[6];
    uint32_t h=H[7];
    for (int i = 0; i < 64; i++) {
        uint32_t S1   = rotr(e,6) ^ rotr(e,11) ^ rotr(e,25);
        uint32_t ch   = (e & f) ^ (~e & g);
        uint32_t t1   = h + S1 + ch + K[i] + W[i];
        uint32_t S0   = rotr(a,2) ^ rotr(a,13) ^ rotr(a,22);
        uint32_t maj  = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2   = S0 + maj;
        h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    H[0]+=a;
    H[1]+=b; 
    H[2]+=c; 
    H[3]+=d; 
    H[4]+=e; 
    H[5]+=f; 
    H[6]+=g; 
    H[7]+=h;
}

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^[[bb4:[0-9]+]]():
// CHECK-NEXT:     "llvm.module_flags"() {{.*}} : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}"sym_name" = "sha256_block"{{.*}}}> ({
// CHECK-NEXT:       ^[[bb7:[0-9]+]](%[[varg7_0:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_1:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_2:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_3:[a-zA-Z0-9_]+]] : !llvm.ptr):
// CHECK-NEXT:         %[[v8:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         %[[v9:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
// CHECK-NEXT:         %[[v10:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 64 : i32}> : () -> i32
// CHECK-NEXT:         %[[v11:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:         %[[v12:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[v13:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:         %[[v14:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK-NEXT:         %[[v15:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
// CHECK-NEXT:         %[[v16:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 5 : i64}> : () -> i64
// CHECK-NEXT:         %[[v17:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 6 : i64}> : () -> i64
// CHECK-NEXT:         %[[v18:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 7 : i64}> : () -> i64
// CHECK-NEXT:         %[[v19:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
// CHECK-NEXT:         %[[v20:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
// CHECK-NEXT:         %[[v21:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
// CHECK-NEXT:         %[[v22:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 25 : i32}> : () -> i32
// CHECK-NEXT:         %[[v23:[0-9]+]] = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v24:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// CHECK-NEXT:         %[[v25:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:         %[[v26:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 22 : i32}> : () -> i32
// CHECK-NEXT:         %[[v27:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v28:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
// CHECK-NEXT:         %[[v29:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:         %[[v30:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 18 : i32}> : () -> i32
// CHECK-NEXT:         %[[v31:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:         %[[v32:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 17 : i32}> : () -> i32
// CHECK-NEXT:         %[[v33:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 19 : i32}> : () -> i32
// CHECK-NEXT:         %[[v34:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb35:[0-9]+]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb35]](%[[varg35_0:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT:         %[[v37:[0-9]+]] = "llvm.icmp"(%[[varg35_0]], %[[v9]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v37]]) [^[[bb38:[0-9]+]], ^[[bb39:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb38]]():
// CHECK-NEXT:         %[[v41:[0-9]+]] = "llvm.sext"(%[[varg35_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v42:[0-9]+]] = "llvm.getelementptr"(%[[varg7_1]], %[[v41]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v43:[0-9]+]] = "llvm.load"(%[[v42]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v45:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v41]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v43]], %[[v45]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb47:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb47]]():
// CHECK-NEXT:         %[[v49:[0-9]+]] = "llvm.add"(%[[varg35_0]], %[[v27]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v49]]) [^[[bb35]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb39]]():
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb51:[0-9]+]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb51]](%[[varg51_0:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT:         %[[v53:[0-9]+]] = "llvm.icmp"(%[[varg51_0]], %[[v10]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v53]]) [^[[bb54:[0-9]+]], ^[[bb55:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb54]]():
// CHECK-NEXT:         %[[v57:[0-9]+]] = "llvm.sub"(%[[varg51_0]], %[[v28]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v58:[0-9]+]] = "llvm.sext"(%[[v57]]) : (i32) -> i64
// CHECK-NEXT:         %[[v59:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v58]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v60:[0-9]+]] = "llvm.load"(%[[v59]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v61:[0-9]+]] = "llvm.lshr"(%[[v60]], %[[v29]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v62:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v29]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v63:[0-9]+]] = "llvm.shl"(%[[v60]], %[[v62]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v64:[0-9]+]] = "llvm.or"(%[[v61]], %[[v63]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v67:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v58]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v68:[0-9]+]] = "llvm.load"(%[[v67]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v69:[0-9]+]] = "llvm.lshr"(%[[v68]], %[[v30]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v70:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v30]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v71:[0-9]+]] = "llvm.shl"(%[[v68]], %[[v70]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v72:[0-9]+]] = "llvm.or"(%[[v69]], %[[v71]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v73:[0-9]+]] = "llvm.xor"(%[[v64]], %[[v72]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v76:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v58]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v77:[0-9]+]] = "llvm.load"(%[[v76]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v78:[0-9]+]] = "llvm.lshr"(%[[v77]], %[[v31]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v79:[0-9]+]] = "llvm.xor"(%[[v73]], %[[v78]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v80:[0-9]+]] = "llvm.sub"(%[[varg51_0]], %[[v24]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v81:[0-9]+]] = "llvm.sext"(%[[v80]]) : (i32) -> i64
// CHECK-NEXT:         %[[v82:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v81]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v83:[0-9]+]] = "llvm.load"(%[[v82]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v84:[0-9]+]] = "llvm.lshr"(%[[v83]], %[[v32]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v85:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v32]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v86:[0-9]+]] = "llvm.shl"(%[[v83]], %[[v85]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v87:[0-9]+]] = "llvm.or"(%[[v84]], %[[v86]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v90:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v81]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v91:[0-9]+]] = "llvm.load"(%[[v90]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v92:[0-9]+]] = "llvm.lshr"(%[[v91]], %[[v33]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v93:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v33]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v94:[0-9]+]] = "llvm.shl"(%[[v91]], %[[v93]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v95:[0-9]+]] = "llvm.or"(%[[v92]], %[[v94]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v96:[0-9]+]] = "llvm.xor"(%[[v87]], %[[v95]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v99:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v81]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v100:[0-9]+]] = "llvm.load"(%[[v99]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v101:[0-9]+]] = "llvm.lshr"(%[[v100]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v102:[0-9]+]] = "llvm.xor"(%[[v96]], %[[v101]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v103:[0-9]+]] = "llvm.sub"(%[[varg51_0]], %[[v9]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v104:[0-9]+]] = "llvm.sext"(%[[v103]]) : (i32) -> i64
// CHECK-NEXT:         %[[v105:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v104]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v106:[0-9]+]] = "llvm.load"(%[[v105]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v107:[0-9]+]] = "llvm.add"(%[[v106]], %[[v79]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v108:[0-9]+]] = "llvm.sub"(%[[varg51_0]], %[[v29]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v109:[0-9]+]] = "llvm.sext"(%[[v108]]) : (i32) -> i64
// CHECK-NEXT:         %[[v110:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v109]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v111:[0-9]+]] = "llvm.load"(%[[v110]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v112:[0-9]+]] = "llvm.add"(%[[v107]], %[[v111]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v113:[0-9]+]] = "llvm.add"(%[[v112]], %[[v102]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v114:[0-9]+]] = "llvm.sext"(%[[varg51_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v115:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v114]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v113]], %[[v115]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb117:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb117]]():
// CHECK-NEXT:         %[[v119:[0-9]+]] = "llvm.add"(%[[varg51_0]], %[[v27]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v119]]) [^[[bb51]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb55]]():
// CHECK-NEXT:         %[[v121:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v11]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v122:[0-9]+]] = "llvm.load"(%[[v121]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v123:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v12]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v124:[0-9]+]] = "llvm.load"(%[[v123]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v125:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v13]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v126:[0-9]+]] = "llvm.load"(%[[v125]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v127:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v14]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v128:[0-9]+]] = "llvm.load"(%[[v127]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v129:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v15]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v130:[0-9]+]] = "llvm.load"(%[[v129]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v131:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v16]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v132:[0-9]+]] = "llvm.load"(%[[v131]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v133:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v17]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v134:[0-9]+]] = "llvm.load"(%[[v133]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v135:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v18]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v136:[0-9]+]] = "llvm.load"(%[[v135]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v130]], %[[v132]], %[[v134]], %[[v136]], %[[v8]], %[[v128]], %[[v126]], %[[v124]], %[[v122]]) [^[[bb137:[0-9]+]]] : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[bb137]](%[[varg137_0:[a-zA-Z0-9_]+]] : i32, %[[varg137_1:[a-zA-Z0-9_]+]] : i32, %[[varg137_2:[a-zA-Z0-9_]+]] : i32, %[[varg137_3:[a-zA-Z0-9_]+]] : i32, %[[varg137_4:[a-zA-Z0-9_]+]] : i32, %[[varg137_5:[a-zA-Z0-9_]+]] : i32, %[[varg137_6:[a-zA-Z0-9_]+]] : i32, %[[varg137_7:[a-zA-Z0-9_]+]] : i32, %[[varg137_8:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT:         %[[v139:[0-9]+]] = "llvm.icmp"(%[[varg137_4]], %[[v10]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v139]]) [^[[bb140:[0-9]+]], ^[[bb141:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb140]]():
// CHECK-NEXT:         %[[v143:[0-9]+]] = "llvm.lshr"(%[[varg137_0]], %[[v19]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v144:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v19]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v145:[0-9]+]] = "llvm.shl"(%[[varg137_0]], %[[v144]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v146:[0-9]+]] = "llvm.or"(%[[v143]], %[[v145]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v147:[0-9]+]] = "llvm.lshr"(%[[varg137_0]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v148:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v21]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v149:[0-9]+]] = "llvm.shl"(%[[varg137_0]], %[[v148]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v150:[0-9]+]] = "llvm.or"(%[[v147]], %[[v149]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v151:[0-9]+]] = "llvm.xor"(%[[v146]], %[[v150]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v152:[0-9]+]] = "llvm.lshr"(%[[varg137_0]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v153:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v22]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v154:[0-9]+]] = "llvm.shl"(%[[varg137_0]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v155:[0-9]+]] = "llvm.or"(%[[v152]], %[[v154]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v156:[0-9]+]] = "llvm.xor"(%[[v151]], %[[v155]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v157:[0-9]+]] = "llvm.and"(%[[varg137_0]], %[[varg137_1]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v158:[0-9]+]] = "llvm.xor"(%[[varg137_0]], %[[v23]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v159:[0-9]+]] = "llvm.and"(%[[v158]], %[[varg137_2]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v160:[0-9]+]] = "llvm.xor"(%[[v157]], %[[v159]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v161:[0-9]+]] = "llvm.add"(%[[varg137_3]], %[[v156]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v162:[0-9]+]] = "llvm.add"(%[[v161]], %[[v160]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v163:[0-9]+]] = "llvm.sext"(%[[varg137_4]]) : (i32) -> i64
// CHECK-NEXT:         %[[v164:[0-9]+]] = "llvm.getelementptr"(%[[varg7_2]], %[[v163]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v165:[0-9]+]] = "llvm.load"(%[[v164]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v166:[0-9]+]] = "llvm.add"(%[[v162]], %[[v165]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v168:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v163]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v169:[0-9]+]] = "llvm.load"(%[[v168]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v170:[0-9]+]] = "llvm.add"(%[[v166]], %[[v169]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v171:[0-9]+]] = "llvm.lshr"(%[[varg137_8]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v172:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v24]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v173:[0-9]+]] = "llvm.shl"(%[[varg137_8]], %[[v172]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v174:[0-9]+]] = "llvm.or"(%[[v171]], %[[v173]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v175:[0-9]+]] = "llvm.lshr"(%[[varg137_8]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v176:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v25]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v177:[0-9]+]] = "llvm.shl"(%[[varg137_8]], %[[v176]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v178:[0-9]+]] = "llvm.or"(%[[v175]], %[[v177]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v179:[0-9]+]] = "llvm.xor"(%[[v174]], %[[v178]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v180:[0-9]+]] = "llvm.lshr"(%[[varg137_8]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v181:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v26]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v182:[0-9]+]] = "llvm.shl"(%[[varg137_8]], %[[v181]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v183:[0-9]+]] = "llvm.or"(%[[v180]], %[[v182]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v184:[0-9]+]] = "llvm.xor"(%[[v179]], %[[v183]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v185:[0-9]+]] = "llvm.and"(%[[varg137_8]], %[[varg137_7]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v186:[0-9]+]] = "llvm.and"(%[[varg137_8]], %[[varg137_6]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v187:[0-9]+]] = "llvm.xor"(%[[v185]], %[[v186]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v188:[0-9]+]] = "llvm.and"(%[[varg137_7]], %[[varg137_6]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v189:[0-9]+]] = "llvm.xor"(%[[v187]], %[[v188]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v190:[0-9]+]] = "llvm.add"(%[[v184]], %[[v189]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v191:[0-9]+]] = "llvm.add"(%[[varg137_5]], %[[v170]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v192:[0-9]+]] = "llvm.add"(%[[v170]], %[[v190]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"() [^[[bb193:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb193]]():
// CHECK-NEXT:         %[[v195:[0-9]+]] = "llvm.add"(%[[varg137_4]], %[[v27]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v191]], %[[varg137_0]], %[[varg137_1]], %[[varg137_2]], %[[v195]], %[[varg137_6]], %[[varg137_7]], %[[varg137_8]], %[[v192]]) [^[[bb137]]] : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[bb141]]():
// CHECK-NEXT:         %[[v197:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v11]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v198:[0-9]+]] = "llvm.load"(%[[v197]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v199:[0-9]+]] = "llvm.add"(%[[v198]], %[[varg137_8]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v199]], %[[v197]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v201:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v12]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v202:[0-9]+]] = "llvm.load"(%[[v201]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v203:[0-9]+]] = "llvm.add"(%[[v202]], %[[varg137_7]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v203]], %[[v201]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v205:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v13]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v206:[0-9]+]] = "llvm.load"(%[[v205]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v207:[0-9]+]] = "llvm.add"(%[[v206]], %[[varg137_6]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v207]], %[[v205]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v209:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v14]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v210:[0-9]+]] = "llvm.load"(%[[v209]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v211:[0-9]+]] = "llvm.add"(%[[v210]], %[[varg137_5]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v211]], %[[v209]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v213:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v15]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v214:[0-9]+]] = "llvm.load"(%[[v213]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v215:[0-9]+]] = "llvm.add"(%[[v214]], %[[varg137_0]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v215]], %[[v213]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v217:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v16]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v218:[0-9]+]] = "llvm.load"(%[[v217]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v219:[0-9]+]] = "llvm.add"(%[[v218]], %[[varg137_1]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v219]], %[[v217]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v221:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v17]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v222:[0-9]+]] = "llvm.load"(%[[v221]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v223:[0-9]+]] = "llvm.add"(%[[v222]], %[[varg137_2]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v223]], %[[v221]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v225:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v18]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v226:[0-9]+]] = "llvm.load"(%[[v225]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v227:[0-9]+]] = "llvm.add"(%[[v226]], %[[varg137_3]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v227]], %[[v225]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()
