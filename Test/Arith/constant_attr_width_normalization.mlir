// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{sym_name = "constants", function_type = () -> ()}> ({
    %0 = "arith.constant"() <{value = 200 : i8}> : () -> i8
    %1 = "arith.constant"() <{value = 3 : i2}> : () -> i2
    %2 = "arith.constant"() <{value = 4294967295 : i32}> : () -> i32
    %3 = "arith.constant"() <{value = -1 : i1}> : () -> i1
    // Already normalized: must round-trip unchanged.
    %4 = "arith.constant"() <{value = -3 : i8}> : () -> i8
    %5 = "arith.constant"() <{value = true}> : () -> i1
    %6 = "arith.constant"() <{value = 300 : i32}> : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "arith.constant"() <{"value" = -56 : i8}> : () -> i8
// CHECK-NEXT: "arith.constant"() <{"value" = -1 : i2}> : () -> i2
// CHECK-NEXT: "arith.constant"() <{"value" = -1 : i32}> : () -> i32
// CHECK-NEXT: "arith.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT: "arith.constant"() <{"value" = -3 : i8}> : () -> i8
// CHECK-NEXT: "arith.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT: "arith.constant"() <{"value" = 300 : i32}> : () -> i32
