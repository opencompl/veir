// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64 | filecheck %s

// The legalizer widens the `i1` condition of the `g_brcond` to `i64` with a `g_zext`
// (`widenBrcondCondition`), which it then lowers to a masked `g_anyext`; the `i32` add is legalized
// as usual.

// CHECK:      "gmir_riscv.g_addw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK:      %[[EXT:.*]] = "gmir.g_anyext"(%{{.*}}) : (i1) -> i64
// CHECK-NEXT: %[[MASK:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: %[[AND:.*]] = "gmir.g_and"(%[[EXT]], %[[MASK]]) : (i64, i64) -> i64
// CHECK-NEXT: "gmir.g_brcond"(%[[AND]]) [^{{.*}}, ^{{.*}}] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i64) -> ()

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i32, i1) -> i32}> ({
  ^bb0(%a : i32, %c : i1):
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %b = "llvm.add"(%a, %one) : (i32, i32) -> i32
    "llvm.cond_br"(%c) [^yes, ^no] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^yes:
    "func.return"(%b) : (i32) -> ()
  ^no:
    "func.return"(%a) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
