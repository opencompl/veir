// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP
//
// veir models no LLVM struct type, so an aggregate zero is carried as an
// unregistered type. Registering `llvm.mlir.zero` must not make that a
// verification failure: a module that only needed
// --allow-unregistered-dialect has to keep working exactly as before.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "aggregates"}> ({
    %arr = "llvm.mlir.zero"() : () -> !llvm.array<4 x ptr>
    %str = "llvm.mlir.zero"() : () -> !llvm.struct<(ptr, i32)>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %{{.*}} = "llvm.mlir.zero"() : () -> !llvm.array<4 x !llvm.ptr>
// CHECK-NEXT: %{{.*}} = "llvm.mlir.zero"() : () -> !llvm.struct<(ptr, i32)>
