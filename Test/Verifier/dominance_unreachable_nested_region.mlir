// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// The entry block's value dominates uses nested inside an unreachable block.
// The nested region's entry is reachable within that region, so its operand
// uses are still verified even though the enclosing block is unreachable.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
  ^entry:
    %v = "arith.constant"() <{value = 42 : i32}> : () -> i32
    "func.return"() : () -> ()
  ^dead:
    "test.test"() ({
      %x = "arith.addi"(%v, %v) : (i32, i32) -> i32
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[V:.*]] = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
// CHECK-NEXT: "func.return"() : () -> ()
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "test.test"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: %{{.*}} = "arith.addi"(%[[V]], %[[V]]) : (i32, i32) -> i32
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: "func.return"() : () -> ()
