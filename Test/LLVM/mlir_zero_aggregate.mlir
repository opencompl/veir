// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// Aggregate zeros of array and struct type must verify and round-trip.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "aggregates"}> ({
    %arr = "llvm.mlir.zero"() : () -> !llvm.array<4 x ptr>
    %str = "llvm.mlir.zero"() : () -> !llvm.struct<(ptr, i32)>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %{{.*}} = "llvm.mlir.zero"() : () -> !llvm.array<4 x !llvm.ptr>
// CHECK-NEXT: %{{.*}} = "llvm.mlir.zero"() : () -> !llvm.struct<(!llvm.ptr, i32)>
