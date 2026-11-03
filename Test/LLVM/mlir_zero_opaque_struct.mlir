// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
// XFAIL: *
//
// VeIR rejects opaque LLVM struct types for now.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "opaque_zero"}> ({
    %opq = "llvm.mlir.zero"() : () -> !llvm.struct<"opaque_t", opaque>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: %{{.*}} = "llvm.mlir.zero"() : () -> !llvm.struct<"opaque_t", opaque>
