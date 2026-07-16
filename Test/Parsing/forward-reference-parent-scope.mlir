// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_VALID

// A use inside a nested region may forward-reference a value defined later in
// the parent region. The nested region is a multi-block graph region, and the
// use sits in a block that is unreachable from the region's entry block, so
// dominance is not checked there (like MLIR; see dominance_graph_capture.mlir)
// and the program verifies. The use must bind to the parent region's %a.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "test.test"() ({
    ^entry():
      "test.test"() : () -> ()
    ^inner():
      "test.test"(%a) : (i32) -> ()
    }) : () -> ()
    %a = "test.test"() : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{{.*}}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         "test.test"() ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             "test.test"() : () -> ()
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             "test.test"(%[[A:.*]]) : (i32) -> ()
// CHECK-NEXT:         }) : () -> ()
// CHECK-NEXT:         %[[A]] = "test.test"() : () -> i32
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
