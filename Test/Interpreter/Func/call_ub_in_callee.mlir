// RUN: veir-interpret %s | filecheck %s

// UB in a callee is reported at the operation of the callee that triggers it, not at the call.

"builtin.module"() ({
  "func.func"() <{sym_name = "div", function_type = (i8, i8) -> i8}> ({
  ^bb0(%a: i8, %b: i8):
    %r = "arith.divsi"(%a, %b) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %c0 = "arith.constant"() <{value = 0 : i8}> : () -> i8
    %r = "func.call"(%c1, %c0) <{callee = @div}> : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      Undefined behavior
// CHECK-NEXT: call_ub_in_callee.mlir:8:5: note: triggered here
// CHECK-NEXT:     %r = "arith.divsi"(%a, %b) : (i8, i8) -> i8
