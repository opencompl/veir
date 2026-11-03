// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `llvm.mlir.zero` materializes the zero of its result type, with no operands
// and no attributes: the null pointer, a zeroed integer, positive zero.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<!llvm.ptr ()>, linkage = #llvm.linkage<external>, sym_name = "nulls"}> ({
    %null = "llvm.mlir.zero"() : () -> !llvm.ptr
    %zero_i32 = "llvm.mlir.zero"() : () -> i32
    %zero_i1 = "llvm.mlir.zero"() : () -> i1
    %zero_f64 = "llvm.mlir.zero"() : () -> f64
    "llvm.return"(%null) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// The func header is not pinned: mlir-opt fills in default attributes on the
// way through, and this test is about the zeros.
// CHECK:      %{{.*}} = "llvm.mlir.zero"() : () -> !llvm.ptr
// CHECK-NEXT: %{{.*}} = "llvm.mlir.zero"() : () -> i32
// CHECK-NEXT: %{{.*}} = "llvm.mlir.zero"() : () -> i1
// CHECK-NEXT: %{{.*}} = "llvm.mlir.zero"() : () -> f64
// CHECK-NEXT: "llvm.return"(%{{.*}}) : (!llvm.ptr) -> ()
