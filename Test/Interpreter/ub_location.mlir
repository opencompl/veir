// RUN: veir-interpret %s | filecheck %s

// Check that UB is reported at the source location of the operation that triggered it.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %a = "arith.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %z = "arith.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %r = "arith.divsi"(%a, %z) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      Undefined behavior
// CHECK-NEXT: ub_location.mlir:8:5: note: triggered here
// CHECK-NEXT:     %r = "arith.divsi"(%a, %z) : (i8, i8) -> i8
// CHECK-NEXT:     ^
