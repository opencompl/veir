// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,postlegalizer-combiner-riscv64,isel-br-riscv64,isel-riscv64,isel-abi-riscv64,reconcile-cast,riscv-combine,dce | filecheck %s

// `isel-br-riscv64` runs before `isel-riscv64`, so a comparison against a constant that only
// feeds a branch becomes a compare-and-branch instead of `slti` and `bnez`. A comparison that is
// also used as a value is still selected as `slti` for that use.

"builtin.module"() ({
  // CHECK-LABEL: @br64
  // CHECK-NOT:   "riscv.slti"
  // CHECK:       "riscv_cf.blt"
  "func.func"() <{sym_name = "br64", function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %p = "llvm.icmp"(%x, %c) <{predicate = 2 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%p)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "func.return"(%c) : (i64) -> ()
  ^bb2:
    "func.return"(%x) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: @br32
  // CHECK-NOT:   "riscv.sltiu"
  // CHECK:       "riscv_cf.bltu"
  "func.func"() <{sym_name = "br32", function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = -3 : i32}> : () -> i32
    %p = "llvm.icmp"(%x, %c) <{predicate = 6 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%p)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "func.return"(%c) : (i32) -> ()
  ^bb2:
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: @both
  // CHECK-DAG:   "riscv.slti"(%{{.*}}) <{"value" = 5 : i64}>
  // CHECK-DAG:   "riscv_cf.blt"
  "func.func"() <{sym_name = "both", function_type = (i64) -> i1}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %p = "llvm.icmp"(%x, %c) <{predicate = 2 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%p)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "func.return"(%p) : (i1) -> ()
  ^bb2:
    "func.return"(%p) : (i1) -> ()
  }) : () -> ()
}) : () -> ()
