// RUN: not veir-interpret %s 2>&1 | filecheck %s

// A call that passes fewer values than its callee takes cannot be interpreted.

"builtin.module"() ({
  "func.func"() <{sym_name = "foo", function_type = (i32, i32) -> i32}> ({
  ^bb0(%a: i32, %b: i32):
    %r = "arith.addi"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %c1 = "arith.constant"() <{value = 1 : i32}> : () -> i32
    %r = "func.call"(%c1) <{callee = @foo}> : (i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: call_wrong_arity.mlir:13:5: error: failed to interpret operation
