// RUN: not veir-interpret %s 2>&1 | filecheck %s

// A failure in a callee is reported at the operation of the callee that fails, not at the call.

"builtin.module"() ({
  "func.func"() <{sym_name = "foo", function_type = () -> i32}> ({
    %r = "func.call"() <{callee = @missing}> : () -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %r = "func.call"() <{callee = @foo}> : () -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      call_fail_in_callee.mlir:7:5: error: failed to interpret operation
// CHECK-NEXT:     %r = "func.call"() <{callee = @missing}> : () -> i32
