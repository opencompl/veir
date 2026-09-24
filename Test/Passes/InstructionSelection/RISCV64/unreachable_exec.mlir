// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// Reaching `llvm.unreachable` is undefined behaviour, and so is reaching the
// `riscv_cf.unreachable` it is lowered to.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %c = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
      %x = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
      "llvm.cond_br"(%c) [^bb1, ^bb2] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb1:
      "llvm.return"(%x) : (i64) -> ()
    ^bb2:
      "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
