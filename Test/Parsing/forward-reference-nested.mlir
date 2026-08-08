// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s

// A value name forward-referenced before its definition resolves to the FIRST textual
// definition of that name, wherever it appears -- following MLIR's generic-form parser,
// whose SSA name table is flat across regions. Here both uses of %a (the one in the function
// body and the one inside the nested region) bind to the first definition, which is inside
// the nested region; the later definition in the function body is an independent value.
// For details see `ForwardValue` in `Veir.Parser.MlirParser`.
//
// That binding makes the outer use refer to a value defined in a nested region, which
// is invalid SSA scoping, so the program parses but fails verification (mlir-opt also
// rejects it). The error below only arises because the outer use was bound to the
// nested definition rather than to the later definition in the function body.

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

// CHECK: uses a value defined outside the isolated region that encloses its use
