// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// Within a block, a block argument dominates every operation, starting with the
// first one, and an operation's result dominates every later operation. This
// includes uses nested in the regions of those operations.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "first_op_region"}> ({
  ^bb0(%a : i32):
    "test.test"() ({
      "test.test"(%a) : (i32) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{function_type = (i32) -> (), sym_name = "later_ops"}> ({
  ^bb0(%a : i32):
    %x = "arith.addi"(%a, %a) : (i32, i32) -> i32
    "test.test"() ({
      "test.test"(%a, %x) : (i32, i32) -> ()
    }) : () -> ()
    %y = "arith.addi"(%x, %a) : (i32, i32) -> i32
    "test.test"() ({
      "test.test"() ({
        "test.test"(%a, %x, %y) : (i32, i32, i32) -> ()
      }) : () -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "sym_name" = "first_op_region"
// CHECK-NEXT: ^{{.*}}(%[[A:.*]] : i32):
// CHECK-NEXT:   "test.test"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "test.test"(%[[A]]) : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK:      "sym_name" = "later_ops"
// CHECK-NEXT: ^{{.*}}(%[[B:.*]] : i32):
// CHECK-NEXT:   %[[X:.*]] = "arith.addi"(%[[B]], %[[B]]) : (i32, i32) -> i32
// CHECK-NEXT:   "test.test"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "test.test"(%[[B]], %[[X]]) : (i32, i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT:   %[[Y:.*]] = "arith.addi"(%[[X]], %[[B]]) : (i32, i32) -> i32
// CHECK-NEXT:   "test.test"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "test.test"() ({
// CHECK-NEXT:     ^{{.*}}():
// CHECK-NEXT:       "test.test"(%[[B]], %[[X]], %[[Y]]) : (i32, i32, i32) -> ()
