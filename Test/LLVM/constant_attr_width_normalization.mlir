// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "constants", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = 200 : i8}> : () -> i8
    %1 = "llvm.mlir.constant"() <{value = 3 : i2}> : () -> i2
    %2 = "llvm.mlir.constant"() <{value = 4294967295 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    // Already normalized: must round-trip unchanged.
    %4 = "llvm.mlir.constant"() <{value = -3 : i8}> : () -> i8
    %5 = "llvm.mlir.constant"() <{value = true}> : () -> i1
    %6 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.mlir.constant"() <{"value" = -56 : i8}> : () -> i8
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = -1 : i2}> : () -> i2
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = -3 : i8}> : () -> i8
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = 300 : i32}> : () -> i32
