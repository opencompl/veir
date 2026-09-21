// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// `arith.constant` reads its `value` property through the same
// `IntegerAttr.ofLiteral` as `llvm.mlir.constant`, so an in-range literal that
// is not already normalized is reduced to the attribute's declared width:
//
//   mlir-opt:  arith.constant 200 : i8         -> arith.constant -56 : i8
//              arith.constant 3 : i2           -> arith.constant -1 : i2
//              arith.constant 4294967295 : i32 -> arith.constant -1 : i32
//              arith.constant -1 : i1          -> arith.constant true
//
// As in Test/LLVM/constant_attr_width_normalization.mlir, Veir prints a width-1
// attribute as `1 : i1` where MLIR prints `true`; only the value is pinned.

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
