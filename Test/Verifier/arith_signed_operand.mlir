// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// An `arith` operation may not accept a signed integer value.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (si8) -> ()}> ({
  ^bb0(%arg0: si8):
    %x = "arith.addi"(%arg0, %arg0) : (si8, si8) -> si8
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.addi: operand 0 must be a signless integer, but got si8
