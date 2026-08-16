// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// func.func is isolated from above: @inner may not capture %k from @outer.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "outer"}> ({
    %k = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
    "func.func"() <{function_type = () -> (), sym_name = "inner"}> ({
      "test.test"(%k) : (i64) -> ()
      "func.return"() : () -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: operand uses a value defined outside the isolated region
