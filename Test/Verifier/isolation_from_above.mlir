// RUN: not veir-opt %s 2>&1 | filecheck %s

// func.func is isolated from above: the body of @inner may not reference %k,
// which is defined in the enclosing function @outer.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "outer"}> ({
  ^bb0():
    %k = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
    "func.func"() <{function_type = () -> (), sym_name = "inner"}> ({
    ^bb1():
      "test.test"(%k) : (i64) -> ()
      "func.return"() : () -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: uses a value defined outside the isolated region
