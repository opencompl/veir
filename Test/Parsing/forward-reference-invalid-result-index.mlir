// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %b = "test.test"(%a#1) : (i32) -> i1
    %a = "test.test"() : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:forward-reference-invalid-result-index.mlir:6:5: error: definition of value %a provides 1 results, but result #1 was used
// CHECK-NEXT:    %a = "test.test"() : () -> i32
// CHECK-NEXT:    ^
// CHECK-NEXT:forward-reference-invalid-result-index.mlir:5:22: note: value used here
// CHECK-NEXT:    %b = "test.test"(%a#1) : (i32) -> i1
// CHECK-NEXT:                     ^
