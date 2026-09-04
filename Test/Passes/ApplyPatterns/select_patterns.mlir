// RUN: veir-opt %s '-p=apply-patterns{muli-two-to-addi}' | filecheck %s --check-prefix=SELECTED
// RUN: veir-opt %s '-p=apply-patterns{addi-zero-to-x}' | filecheck %s --check-prefix=UNSELECTED

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %two = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
      %x = "test.test"() : () -> i32
      %mul_two = "llvm.mul"(%x, %two) : (i32, i32) -> i32
      "test.test"(%mul_two) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// The muli-two-to-addi is selected, so the optimization triggered

// SELECTED:     %[[X:.*]] = "test.test"() : () -> i32
// SELECTED-NEXT: %[[ADD:.*]] = "llvm.add"(%[[X]], %[[X]]) : (i32, i32) -> i32
// SELECTED-NEXT: "test.test"(%[[ADD]]) : (i32) -> ()
// SELECTED-NOT: "llvm.mul"

// The muli-two-to-addi is unselected, so the optimization did not trigger

// UNSELECTED:     %[[TWO:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// UNSELECTED-NEXT: %[[X:.*]] = "test.test"() : () -> i32
// UNSELECTED-NEXT: %[[MUL:.*]] = "llvm.mul"(%[[X]], %[[TWO]]) : (i32, i32) -> i32
// UNSELECTED-NEXT: "test.test"(%[[MUL]]) : (i32) -> ()
