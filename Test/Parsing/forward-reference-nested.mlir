// RUN: veir-opt %s --allow-unregistered-dialect | filecheck %s

// A value name forward-referenced before its definition resolves to the FIRST textual
// definition of that name, wherever it appears -- following MLIR's generic-form parser,
// whose SSA name table is flat across regions. Here both uses of %a (the one in the function
// body and the one inside the nested region) bind to the first definition, which is inside
// the nested region; the later definition in the function body is an independent value.
//
// Whether this is legal under dominance / IsolatedFromAbove is a verifier concern that MLIR
// checks after parsing. Implementation in VeIR TBD. For details see `ForwardValue` in 
// `Veir.Parser.MlirParser`.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "test.use"(%a) : (i32) -> ()
    "test.wrapper"() ({
    ^inner:
      "test.use"(%a) : (i32) -> ()
      %a = "test.def"() : () -> i32
      "cf.br"() [^inner] : () -> ()
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
