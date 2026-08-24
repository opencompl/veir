// RUN: veir-opt %s --disable-verifiers | filecheck %s
// RUN: not veir-opt %s 2>&1 | filecheck %s --check-prefix=VERIFY
// RUN: MLIR_INVALID

// The parser resolves `%a` inside the nested region to the definition in the
// enclosing function body. That name resolution is what this test pins down;
// the resulting IR is not valid, because the definition appears after the
// operation that encloses the use, so it does not dominate it. A graph region
// relaxes the ordering between points *inside* the region, not the dominance
// of values it captures from an enclosing SSACFG region.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "test.test"() ({
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
// CHECK-NEXT:             "test.test"(%[[A:.*]]) : (i32) -> ()
// CHECK-NEXT:         }) : () -> ()
// CHECK-NEXT:         %[[A]] = "test.test"() : () -> i32
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()

// VERIFY: operand #0 does not dominate this use
