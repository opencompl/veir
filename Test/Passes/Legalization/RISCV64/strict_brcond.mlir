// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64{strict} | filecheck %s
// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64 | filecheck %s --check-prefix=LAX

// The strict legalizer does not widen branch conditions, which `isel-br-riscv64` accepts at any
// width, so the `g_brcond` keeps its `i1` condition; the `i32` add is legalized as usual.

// CHECK: "gmir_riscv.g_addw"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK: "gmir.g_brcond"(%{{.*}}) [^{{.*}}, ^{{.*}}] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()

// LAX: "gmir.g_brcond"(%{{.*}}) [^{{.*}}, ^{{.*}}] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i64) -> ()

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
