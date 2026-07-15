// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// A value that is used but never defined anywhere is reported once top-level parsing
// finishes.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "test.test"(%a) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:forward-reference-missing-value.mlir:8:17: error: use of undefined value %a
// CHECK-NEXT:    "test.test"(%a) : (i32) -> ()
// CHECK-NEXT:                ^
