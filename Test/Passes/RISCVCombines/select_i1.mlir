// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A boolean result needs the condition or its inverse, without an extension.
"builtin.module"() ({
  "func.func"() <{sym_name = "select_i1", function_type = (i1) -> (i1, i1)}> ({
  ^bb0(%cond: i1):
    %one = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %minusOne = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %zero = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    %a = "llvm.select"(%cond, %one, %zero) : (i1, i1, i1) -> i1
    %b = "llvm.select"(%cond, %zero, %minusOne) : (i1, i1, i1) -> i1
    "func.return"(%a, %b) : (i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @select_i1
// CHECK-SAME: (%[[COND:.*]]: i1)
// CHECK-NEXT: %[[ONE:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i1}> : () -> i1
// CHECK-NEXT: %[[NOT:.*]] = "llvm.xor"(%[[COND]], %[[ONE]]) : (i1, i1) -> i1
// CHECK-NEXT: "func.return"(%[[COND]], %[[NOT]]) : (i1, i1) -> ()
