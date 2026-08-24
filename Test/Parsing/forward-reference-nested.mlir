// RUN: veir-opt %s --allow-unregistered-dialect --disable-verifiers | filecheck %s
// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s --check-prefix=VERIFY
// RUN: MLIR_INVALID

// A value name forward-referenced before its definition resolves to the FIRST textual
// definition of that name, wherever it appears -- following MLIR's generic-form parser,
// whose SSA name table is flat across regions. Here both uses of %a (the one in the function
// body and the one inside the nested region) bind to the first definition, which is inside
// the nested region; the later definition in the function body is an independent value.
//
// This is not legal: the outer use reads a value defined in a child
// region, which does not dominate it, and the Veir verifier rejects it
// exactly as MLIR does.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "test.use"(%a) : (i32) -> ()
    "test.wrapper"() ({
      "test.use"(%a) : (i32) -> ()
      %a = "test.def"() : () -> i32
    }) : () -> ()
    %a = "test.def"() : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// Both uses bind to the first (nested) definition ...
// CHECK:        "test.use"(%[[A:.*]]) : (i32) -> ()
// CHECK:            "test.use"(%[[A]]) : (i32) -> ()
// CHECK-NEXT:       %[[A]] = "test.def"() : () -> i32
// ... and the later definition is an independent value.
// CHECK:        %[[B:.*]] = "test.def"() : () -> i32
// CHECK-NOT:    %[[A]] =

// The nested use is fine: an unregistered operation's region is a graph region, where a
// definition need not precede its use. The outer use is not.
// VERIFY: operand #0 does not dominate this use
