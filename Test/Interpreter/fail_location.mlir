// RUN: not veir-interpret %s 2>&1 | filecheck %s

// Check that an error is reported at the source location of the operation that triggered it.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %a = "arith.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %r = "test.unknown"(%a) : (i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      fail_location.mlir:7:5: error: failed to interpret operation
// CHECK-NEXT:     %r = "test.unknown"(%a) : (i8) -> i8
// CHECK-NEXT:     ^
