// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// An `arith` operation may not produce an unsigned integer value.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i8) -> ()}> ({
  ^bb0(%arg0: i8):
    %x = "arith.extui"(%arg0) : (i8) -> ui32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.extui: result 0 must be a signless integer, but got ui32
