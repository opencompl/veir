// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Within a block, an operation's result does not dominate the operations
// before it. The block argument (operand #0) dominates the use, the result
// of the later operation (operand #1) does not.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "main"}> ({
  ^bb0(%a : i32):
    %x = "arith.addi"(%a, %y) : (i32, i32) -> i32
    %y = "arith.addi"(%a, %a) : (i32, i32) -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.addi: operand #1 does not dominate this use
