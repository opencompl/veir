// RUN: ./Tools/vcc --emit-mlir -O %s -o - | filecheck %s
// RUN: ./Tools/vcc -c %s -o %t.o
// RUN: test -s %t.o
// RUN: ./Tools/vcc -S %s -o %t.s
// RUN: test -s %t.s

/* 
    This file contains a very naive implementation of the FastNTT algorithm. 
    It is an example of a real application we should aim to lower with out RISC-V instruction 
    selection. It is also interesting in the vector-extension perspective, 
    which significantly optimizes it. 
    Some references: 
    - https://ieeexplore.ieee.org/document/10177902 
    - https://eprint.iacr.org/2024/585.pdf
    - https://link.springer.com/chapter/10.1007/978-3-031-46077-7_22 
    - https://fprox.substack.com/p/faster-ntt-with-risc-v-vector 
    
    Our implementation is based on the description in HEIR : 
        def fastNTT(coeffs, n, cmod, roots, inverse):
         m = inverse ? n : 2             # m denotes the batchSize or stride
         r = inverse ? 1 : degree / 2    # r denotes the exponent of the root
         for (s = 0; s < log2(n); s++):
           for (k = 0; k < n / m; k++):
             for (j = 0; j < m / 2; j++):
               A = coeffs[k * m + j]
               B = coeffs[k * m + j + m / 2]
               root = roots[(2 * j + 1) * rootExp]
               coeffs[k * m + j], coeffs[k * m + j + m / 2]
                 = bflyOp(A, B, root, cmod)
             end
           end
           m = inverse ? m / 2 : m * 2
           r = inverse ? r * 2 : m / 2
         end
        where bflyOp is one of:
        bflyCT(A, B, root, cmod):
            (A + root * B % cmod, A - root * B % cmod)
    
        bflyGS(A, B, root, cmod):
            (A + B % cmod, (A - B) * root % cmod)
    Reference: https://github.com/google/heir/blob/1210ad37dc9531d6e60d8ddbce81dbd79f7626a6/lib/Dialect/Polynomial/Conversions/PolynomialToModArith/PolynomialToModArith.cpp#L1060 
*/
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

// log2(0) = 0
// log2(1) = 0
// log2(2*n) = 1 + log2(n)
__attribute__((always_inline)) static long log2FloorAux(long n) {
    long result = 0;
    while (n > 1) {
        n >>= 1;
        result++;
    }
    return result;
}

__attribute__((always_inline)) static long log2Floor(long n) {
    return log2FloorAux(n);
}

/* bflyCT */
__attribute__((always_inline)) static void bflyCT(long A, long B, long root, long cmod, long *outA, long *outB) {
    *outA = (A + root * B % cmod) % cmod;
    *outB = (A - root * B % cmod + cmod) % cmod;
}

/* bflyGS */
__attribute__((always_inline)) static void bflyGS(long A, long B, long root, long cmod, long *outA, long *outB) {
    *outA = (A + B) % cmod;
    *outB = (A - B) * root % cmod;
}

__attribute__((always_inline)) static void fastNTT(long *coeffs, long n, long cmod, const long *roots, long inverse, long degree) {
    long m = inverse ? n : 2;
    long r = inverse ? 1 : degree / 2;
    long rootExp = n / 2;

    for (long s = 0; s < log2Floor(n); s++) {
        for (long k = 0; k < n / m; k++) {
            for (long j = 0; j < m / 2; j++) {
                long A    = coeffs[k * m + j];
                long B    = coeffs[k * m + j + m / 2];
                long root = roots[(2 * j + 1) * rootExp];
                long outA, outB;
                bflyCT(A, B, root, cmod, &outA, &outB);
                coeffs[k * m + j]         = outA;
                coeffs[k * m + j + m / 2] = outB;
            }
        }
        rootExp = rootExp / 2;
        m = inverse ? m / 2 : m * 2;
        r = inverse ? r * 2 : r / 2;
    }
}

int main() {
    long n = 4;
    long cmod = 17;
    long degree = 4; 
    long inverse = 0; // 0 for forward NTT, 1 for inverse NTT
    long coeffs[4];
    coeffs[0] = 1;
    coeffs[1] = 2;
    coeffs[2] = 3;
    coeffs[3] = 4;

    long roots_size = n * 2; 
    
    long roots[8]; 
    
    long current_root = 1;
    for (long i = 0; i < 8; i++) {
        roots[i] = current_root;
        current_root = (current_root * 3) % cmod;
    }

    fastNTT(coeffs, n, cmod, roots, inverse, degree);
    
    return 0;
}

// CHECK:      "builtin.module"() ({
// CHECK-NEXT: ^[[BB4:[0-9]+]]():
// CHECK-NEXT:   "llvm.module_flags"()
// CHECK-NEXT:   "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, {{.*}}"function_type" = !llvm.func<i32 ()>, "linkage" = #llvm.linkage<external>, no_inline, no_unwind, {{.*}}"sym_name" = "main"{{.*}}}> ({
// CHECK-NEXT:   ^[[BB7:[0-9]+]]():
// CHECK-NEXT:     %[[M_C1:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:     %[[M_C0:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C1_64:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C2:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C3:.*]] = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C4:.*]] = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C8:.*]] = "llvm.mlir.constant"() <{"value" = 8 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C0_32:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:     %[[M_C17:.*]] = "llvm.mlir.constant"() <{"value" = 17 : i64}> : () -> i64
// CHECK-NEXT:     %[[ALLOC17:.*]] = "llvm.alloca"(%[[M_C1]]) <{"alignment" = {{[0-9]+}} : i64, "elem_type" = !llvm.array<4 x i64>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:     %[[ALLOC18:.*]] = "llvm.alloca"(%[[M_C1]]) <{"alignment" = {{[0-9]+}} : i64, "elem_type" = !llvm.array<8 x i64>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:     %[[GEP19:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C0]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[M_C1_64]], %[[GEP19]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = {{[0-9]+}} : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[GEP21:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C1_64]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[M_C2]], %[[GEP21]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[GEP23:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C2]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[M_C3]], %[[GEP23]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = {{[0-9]+}} : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[GEP25:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C3]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[M_C4]], %[[GEP25]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     "llvm.br"(%[[M_C1_64]], %[[M_C0]]) [^[[BB28:[0-9]+]]] : (i64, i64) -> ()
// CHECK-NEXT:   ^[[BB28]](%[[ARG28_0:.*]] : i64, %[[ARG28_1:.*]] : i64):
// CHECK-NEXT:     %[[CMP30:.*]] = "llvm.icmp"(%[[ARG28_1]], %[[M_C8]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP30]]) [^[[BB31:[0-9]+]], ^[[BB32:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB31]]():
// CHECK-NEXT:     %[[GEP34:.*]] = "llvm.getelementptr"(%[[ALLOC18]], %[[M_C0]], %[[ARG28_1]]) <{"elem_type" = !llvm.array<8 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[ARG28_0]], %[[GEP34]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[MUL36:.*]] = "llvm.mul"(%[[ARG28_0]], %[[M_C3]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[SREM37:.*]] = "llvm.srem"(%[[MUL36]], %[[M_C17]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"() [^[[BB38:[0-9]+]]] : () -> ()
// CHECK-NEXT:   ^[[BB38]]():
// CHECK-NEXT:     %[[ADD40:.*]] = "llvm.add"(%[[ARG28_1]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[SREM37]], %[[ADD40]]) [^[[BB28]]] : (i64, i64) -> ()
// CHECK-NEXT:   ^[[BB32]]():
// CHECK-NEXT:     %[[GEP42:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C0]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[GEP43:.*]] = "llvm.getelementptr"(%[[ALLOC18]], %[[M_C0]], %[[M_C0]]) <{"elem_type" = !llvm.array<8 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[CMP44:.*]] = "llvm.icmp"(%[[M_C0]], %[[M_C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP44]]) [^[[BB45:[0-9]+]], ^[[BB46:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB45]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C4]]) [^[[BB48:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB46]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C2]]) [^[[BB48]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB48]](%[[ARG48_0:.*]] : i64):
// CHECK-NEXT:     %[[CMP51:.*]] = "llvm.icmp"(%[[M_C0]], %[[M_C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP51]]) [^[[BB52:[0-9]+]], ^[[BB53:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB52]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C1_64]]) [^[[BB55:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB53]]():
// CHECK-NEXT:     %[[DIV57:.*]] = "llvm.sdiv"(%[[M_C4]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[DIV57]]) [^[[BB55]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB55]](%[[ARG55_0:.*]] : i64):
// CHECK-NEXT:     %[[DIV59:.*]] = "llvm.sdiv"(%[[M_C4]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[M_C0]], %[[DIV59]], %[[ARG55_0]], %[[ARG48_0]]) [^[[BB60:[0-9]+]]] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT:   ^[[BB60]](%[[ARG60_0:.*]] : i64, %[[ARG60_1:.*]] : i64, %[[ARG60_2:.*]] : i64, %[[ARG60_3:.*]] : i64):
// CHECK-NEXT:     "llvm.br"(%[[M_C0]], %[[M_C4]]) [^[[BB62:[0-9]+]]] : (i64, i64) -> ()
// CHECK-NEXT:   ^[[BB62]](%[[ARG62_0:.*]] : i64, %[[ARG62_1:.*]] : i64):
// CHECK-NEXT:     %[[CMP64:.*]] = "llvm.icmp"(%[[ARG62_1]], %[[M_C1_64]]) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP64]]) [^[[BB65:[0-9]+]], ^[[BB66:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB65]]():
// CHECK-NEXT:     %[[ASHR68:.*]] = "llvm.ashr"(%[[ARG62_1]], %[[M_C1_64]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD69:.*]] = "llvm.add"(%[[ARG62_0]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD69]], %[[ASHR68]]) [^[[BB62]]] : (i64, i64) -> ()
// CHECK-NEXT:   ^[[BB66]]():
// CHECK-NEXT:     %[[CMP71:.*]] = "llvm.icmp"(%[[ARG60_0]], %[[ARG62_0]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP71]]) [^[[BB72:[0-9]+]], ^[[BB73:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB72]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C0]]) [^[[BB75:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB75]](%[[ARG75_0:.*]] : i64):
// CHECK-NEXT:     %[[DIV77:.*]] = "llvm.sdiv"(%[[M_C4]], %[[ARG60_3]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[CMP78:.*]] = "llvm.icmp"(%[[ARG75_0]], %[[DIV77]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP78]]) [^[[BB79:[0-9]+]], ^[[BB80:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB79]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C0]]) [^[[BB82:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB82]](%[[ARG82_0:.*]] : i64):
// CHECK-NEXT:     %[[DIV84:.*]] = "llvm.sdiv"(%[[ARG60_3]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[CMP85:.*]] = "llvm.icmp"(%[[ARG82_0]], %[[DIV84]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP85]]) [^[[BB86:[0-9]+]], ^[[BB87:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB86]]():
// CHECK-NEXT:     %[[MUL89:.*]] = "llvm.mul"(%[[ARG75_0]], %[[ARG60_3]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD90:.*]] = "llvm.add"(%[[MUL89]], %[[ARG82_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[GEP91:.*]] = "llvm.getelementptr"(%[[GEP42]], %[[ADD90]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[LOAD92:.*]] = "llvm.load"(%[[GEP91]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:     %[[DIV95:.*]] = "llvm.sdiv"(%[[ARG60_3]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD96:.*]] = "llvm.add"(%[[ADD90]], %[[DIV95]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[GEP97:.*]] = "llvm.getelementptr"(%[[GEP42]], %[[ADD96]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[LOAD98:.*]] = "llvm.load"(%[[GEP97]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:     %[[MUL99:.*]] = "llvm.mul"(%[[M_C2]], %[[ARG82_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD100:.*]] = "llvm.add"(%[[MUL99]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[MUL101:.*]] = "llvm.mul"(%[[ADD100]], %[[ARG60_1]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[GEP102:.*]] = "llvm.getelementptr"(%[[GEP43]], %[[MUL101]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[LOAD103:.*]] = "llvm.load"(%[[GEP102]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:     %[[MUL104:.*]] = "llvm.mul"(%[[LOAD103]], %[[LOAD98]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[SREM105:.*]] = "llvm.srem"(%[[MUL104]], %[[M_C17]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD106:.*]] = "llvm.add"(%[[LOAD92]], %[[SREM105]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[SREM107:.*]] = "llvm.srem"(%[[ADD106]], %[[M_C17]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[SUB110:.*]] = "llvm.sub"(%[[LOAD92]], %[[SREM105]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD111:.*]] = "llvm.add"(%[[SUB110]], %[[M_C17]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[SREM112:.*]] = "llvm.srem"(%[[ADD111]], %[[M_C17]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[GEP115:.*]] = "llvm.getelementptr"(%[[GEP42]], %[[ADD90]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[SREM107]], %[[GEP115]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[GEP121:.*]] = "llvm.getelementptr"(%[[GEP42]], %[[ADD96]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[SREM112]], %[[GEP121]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[ADD123:.*]] = "llvm.add"(%[[ARG82_0]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD123]]) [^[[BB82]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB87]]():
// CHECK-NEXT:     %[[ADD125:.*]] = "llvm.add"(%[[ARG75_0]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD125]]) [^[[BB75]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB80]]():
// CHECK-NEXT:     %[[DIV127:.*]] = "llvm.sdiv"(%[[ARG60_1]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[CMP128:.*]] = "llvm.icmp"(%[[M_C0]], %[[M_C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP128]]) [^[[BB129:[0-9]+]], ^[[BB130:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB129]]():
// CHECK-NEXT:     %[[DIV132:.*]] = "llvm.sdiv"(%[[ARG60_3]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[DIV132]]) [^[[BB133:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB130]]():
// CHECK-NEXT:     %[[ADD152:.*]] = "llvm.add"(%[[ARG60_3]], %[[ARG60_3]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD152]]) [^[[BB133]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB133]](%[[ARG133_0:.*]] : i64):
// CHECK-NEXT:     %[[CMP137:.*]] = "llvm.icmp"(%[[M_C0]], %[[M_C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP137]]) [^[[BB138:[0-9]+]], ^[[BB139:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB138]]():
// CHECK-NEXT:     %[[ADD151:.*]] = "llvm.add"(%[[ARG60_2]], %[[ARG60_2]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD151]]) [^[[BB142:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB139]]():
// CHECK-NEXT:     %[[DIV144:.*]] = "llvm.sdiv"(%[[ARG60_2]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[DIV144]]) [^[[BB142]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB142]](%[[ARG142_0:.*]] : i64):
// CHECK-NEXT:     %[[ADD146:.*]] = "llvm.add"(%[[ARG60_0]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD146]], %[[DIV127]], %[[ARG142_0]], %[[ARG133_0]]) [^[[BB60]]] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT:   ^[[BB73]]():
// CHECK-NEXT:     "llvm.return"(%[[M_C0_32]]) : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()