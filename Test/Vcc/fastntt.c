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

__attribute__((always_inline)) void fastNTT(long *coeffs, long n, long cmod, const long *roots, long inverse, long degree) {
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


// CHECK: "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
// CHECK-NEXT:     "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, always_inline, "arg_attrs" = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, "frame_pointer" = #llvm.framePointerKind<all>, "function_type" = !llvm.func<void (!llvm.ptr, i64, i64, !llvm.ptr, i64, i64)>, "linkage" = #llvm.linkage<external>, no_unwind, "passthrough" = {{\[\[}}"min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], "sym_name" = "fastNTT", "target_cpu" = "x86-64", "target_features" = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, "tune_cpu" = "generic", "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<async>, "visibility_" = 0 : i64}> ({
// CHECK-NEXT:       ^7(%[[VAL_0:.*]] : !llvm.ptr, %[[VAL_1:.*]] : i64, %[[VAL_2:.*]] : i64, %[[VAL_3:.*]] : !llvm.ptr, %[[VAL_4:.*]] : i64, %[[VAL_5:.*]] : i64):
// CHECK-NEXT:         %[[VAL_6:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:         %[[VAL_7:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:         %[[VAL_8:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[VAL_9:.*]] = "llvm.icmp"(%[[VAL_4]], %[[VAL_6]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_9]]) [^12, ^13] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^12():
// CHECK-NEXT:         "llvm.br"(%[[VAL_1]]) [^15] : (i64) -> ()
// CHECK-NEXT:       ^13():
// CHECK-NEXT:         "llvm.br"(%[[VAL_7]]) [^15] : (i64) -> ()
// CHECK-NEXT:       ^15(%[[VAL_10:.*]] : i64):
// CHECK-NEXT:         %[[VAL_11:.*]] = "llvm.icmp"(%[[VAL_4]], %[[VAL_6]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_11]]) [^19, ^20] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^19():
// CHECK-NEXT:         "llvm.br"(%[[VAL_8]]) [^22] : (i64) -> ()
// CHECK-NEXT:       ^20():
// CHECK-NEXT:         %[[VAL_12:.*]] = "llvm.sdiv"(%[[VAL_5]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_12]]) [^22] : (i64) -> ()
// CHECK-NEXT:       ^22(%[[VAL_13:.*]] : i64):
// CHECK-NEXT:         %[[VAL_14:.*]] = "llvm.sdiv"(%[[VAL_1]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_13]], %[[VAL_14]], %[[VAL_6]], %[[VAL_10]]) [^27] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT:       ^27(%[[VAL_15:.*]] : i64, %[[VAL_16:.*]] : i64, %[[VAL_17:.*]] : i64, %[[VAL_18:.*]] : i64):
// CHECK-NEXT:         "llvm.br"(%[[VAL_6]], %[[VAL_1]]) [^29] : (i64, i64) -> ()
// CHECK-NEXT:       ^29(%[[VAL_19:.*]] : i64, %[[VAL_20:.*]] : i64):
// CHECK-NEXT:         %[[VAL_21:.*]] = "llvm.icmp"(%[[VAL_20]], %[[VAL_8]]) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_21]]) [^32, ^33] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^32():
// CHECK-NEXT:         %[[VAL_22:.*]] = "llvm.ashr"(%[[VAL_20]], %[[VAL_8]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_23:.*]] = "llvm.add"(%[[VAL_19]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_23]], %[[VAL_22]]) [^29] : (i64, i64) -> ()
// CHECK-NEXT:       ^33():
// CHECK-NEXT:         %[[VAL_24:.*]] = "llvm.icmp"(%[[VAL_17]], %[[VAL_19]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_24]]) [^39, ^40] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^39():
// CHECK-NEXT:         "llvm.br"(%[[VAL_6]]) [^42] : (i64) -> ()
// CHECK-NEXT:       ^42(%[[VAL_25:.*]] : i64):
// CHECK-NEXT:         %[[VAL_26:.*]] = "llvm.sdiv"(%[[VAL_1]], %[[VAL_18]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_27:.*]] = "llvm.icmp"(%[[VAL_25]], %[[VAL_26]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_27]]) [^46, ^47] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^46():
// CHECK-NEXT:         "llvm.br"(%[[VAL_6]]) [^49] : (i64) -> ()
// CHECK-NEXT:       ^49(%[[VAL_28:.*]] : i64):
// CHECK-NEXT:         %[[VAL_29:.*]] = "llvm.sdiv"(%[[VAL_18]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_30:.*]] = "llvm.icmp"(%[[VAL_28]], %[[VAL_29]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_30]]) [^53, ^54] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^53():
// CHECK-NEXT:         %[[VAL_31:.*]] = "llvm.mul"(%[[VAL_25]], %[[VAL_18]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_32:.*]] = "llvm.add"(%[[VAL_31]], %[[VAL_28]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_33:.*]] = "llvm.getelementptr"(%[[VAL_0]], %[[VAL_32]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[VAL_34:.*]] = "llvm.load"(%[[VAL_33]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:         %[[VAL_35:.*]] = "llvm.sdiv"(%[[VAL_18]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_36:.*]] = "llvm.add"(%[[VAL_32]], %[[VAL_35]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_37:.*]] = "llvm.getelementptr"(%[[VAL_0]], %[[VAL_36]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[VAL_38:.*]] = "llvm.load"(%[[VAL_37]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:         %[[VAL_39:.*]] = "llvm.mul"(%[[VAL_7]], %[[VAL_28]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_40:.*]] = "llvm.add"(%[[VAL_39]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_41:.*]] = "llvm.mul"(%[[VAL_40]], %[[VAL_16]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_42:.*]] = "llvm.getelementptr"(%[[VAL_3]], %[[VAL_41]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[VAL_43:.*]] = "llvm.load"(%[[VAL_42]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:         %[[VAL_44:.*]] = "llvm.mul"(%[[VAL_43]], %[[VAL_38]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_45:.*]] = "llvm.srem"(%[[VAL_44]], %[[VAL_2]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_46:.*]] = "llvm.add"(%[[VAL_34]], %[[VAL_45]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_47:.*]] = "llvm.srem"(%[[VAL_46]], %[[VAL_2]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_48:.*]] = "llvm.sub"(%[[VAL_34]], %[[VAL_45]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_49:.*]] = "llvm.add"(%[[VAL_48]], %[[VAL_2]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_50:.*]] = "llvm.srem"(%[[VAL_49]], %[[VAL_2]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_51:.*]] = "llvm.getelementptr"(%[[VAL_0]], %[[VAL_32]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[VAL_47]], %[[VAL_51]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[VAL_52:.*]] = "llvm.getelementptr"(%[[VAL_0]], %[[VAL_36]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[VAL_50]], %[[VAL_52]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^90] : () -> ()
// CHECK-NEXT:       ^90():
// CHECK-NEXT:         %[[VAL_53:.*]] = "llvm.add"(%[[VAL_28]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_53]]) [^49] : (i64) -> ()
// CHECK-NEXT:       ^54():
// CHECK-NEXT:         "llvm.br"() [^94] : () -> ()
// CHECK-NEXT:       ^94():
// CHECK-NEXT:         %[[VAL_54:.*]] = "llvm.add"(%[[VAL_25]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_54]]) [^42] : (i64) -> ()
// CHECK-NEXT:       ^47():
// CHECK-NEXT:         %[[VAL_55:.*]] = "llvm.sdiv"(%[[VAL_16]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_56:.*]] = "llvm.icmp"(%[[VAL_4]], %[[VAL_6]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_56]]) [^100, ^101] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^100():
// CHECK-NEXT:         %[[VAL_57:.*]] = "llvm.sdiv"(%[[VAL_18]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_57]]) [^104] : (i64) -> ()
// CHECK-NEXT:       ^101():
// CHECK-NEXT:         %[[VAL_58:.*]] = "llvm.add"(%[[VAL_18]], %[[VAL_18]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_58]]) [^104] : (i64) -> ()
// CHECK-NEXT:       ^104(%[[VAL_59:.*]] : i64):
// CHECK-NEXT:         %[[VAL_60:.*]] = "llvm.icmp"(%[[VAL_4]], %[[VAL_6]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_60]]) [^109, ^110] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^109():
// CHECK-NEXT:         %[[VAL_61:.*]] = "llvm.add"(%[[VAL_15]], %[[VAL_15]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_61]]) [^113] : (i64) -> ()
// CHECK-NEXT:       ^110():
// CHECK-NEXT:         %[[VAL_62:.*]] = "llvm.sdiv"(%[[VAL_15]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_62]]) [^113] : (i64) -> ()
// CHECK-NEXT:       ^113(%[[VAL_63:.*]] : i64):
// CHECK-NEXT:         "llvm.br"() [^117] : () -> ()
// CHECK-NEXT:       ^117():
// CHECK-NEXT:         %[[VAL_64:.*]] = "llvm.add"(%[[VAL_17]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_63]], %[[VAL_55]], %[[VAL_64]], %[[VAL_59]]) [^27] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT:       ^40():
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, "llvm.ident" = "Ubuntu clang version 18.1.3 (1ubuntu1)", "llvm.module_asm" = [], "llvm.target_triple" = "x86_64-pc-linux-gnu"} : () -> ()
