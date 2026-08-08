// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_VALID

// A single-block region of an unregistered/test operation is a graph region,
// where operations may use each other without respecting source order, so this
// use-before-def verifies. This leniency is limited to single-block regions:
// as in MLIR (see getDominanceInfo in mlir/lib/IR/Dominance.cpp), a multi-block
// region always has SSA dominance, whatever operation owns it -- see
// dominance_multi_block_use_before_def.mlir for the rejected multi-block
// counterpart of this program.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "m"}> ({
  ^entry():
    "test.test"() ({
    ^g0():
      "test.test"(%a) : (i64) -> ()
      %a = "test.test"() : () -> i64
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "test.test"(%[[A:.*]]) : (i64) -> ()
// CHECK-NEXT: %[[A]] = "test.test"() : () -> i64
