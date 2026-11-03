// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// An unknown operation does not hide an enclosing function's known isolation
// constraint. Its nested operations still cannot capture the module's value.
"builtin.module"() ({
  %outer = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "func.func"() <{function_type = () -> (), sym_name = "f"}> ({
    "unknown.container"() ({
      "test.test"(%outer) : (i32) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: operand uses a value defined outside the isolated region
