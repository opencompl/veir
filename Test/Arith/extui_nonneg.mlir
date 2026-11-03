// RUN: VEIR_ROUNDTRIP
// RUN: %if mlir-min-23 %{ MLIR_ROUNDTRIP %}

"builtin.module"() ({
  "func.func"() <{function_type = (i8) -> (), sym_name = "f"}> ({
  ^bb0(%c: i8):
    %a = "arith.extui"(%c) <{nonNeg}> : (i8) -> i32
    %b = "arith.extui"(%c) : (i8) -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "arith.extui"(%{{[a-z0-9_]+}}) <{nonNeg}> : (i8) -> i32
// CHECK: "arith.extui"(%{{[a-z0-9_]+}}) : (i8) -> i32
