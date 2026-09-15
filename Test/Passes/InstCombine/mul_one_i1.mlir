// RUN: veir-opt %s -p=instcombine | filecheck %s
// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// At i1, both spellings denote the multiplicative identity. Its signed value
// is -1, but replacing it by unsigned negation would introduce poison.
"builtin.module"() ({
  "func.func"() <{sym_name = "identity", function_type = (i1) -> (i1, i1)}> ({
  ^bb0(%x: i1):
    %one = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %minusOne = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %a = "llvm.mul"(%x, %one) <{overflowFlags = 2 : i32}> : (i1, i1) -> i1
    %b = "llvm.mul"(%x, %minusOne) <{overflowFlags = 2 : i32}> : (i1, i1) -> i1
    "func.return"(%a, %b) : (i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @identity
// CHECK-SAME: (%[[X:.*]]: i1)
// CHECK-NEXT: "func.return"(%[[X]], %[[X]]) : (i1, i1) -> ()
