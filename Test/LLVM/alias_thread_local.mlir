// RUN: VEIR_ROUNDTRIP
// RUN: %if !mlir-min-24 %{ MLIR_ROUNDTRIP %}

// MLIR 24 replaces thread_local_ with tls_mode and drops the old property.
"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 0 : i32}> ({
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = i32, dso_local, linkage = #llvm.linkage<private>, sym_name = "a", thread_local_, unnamed_addr = 1 : i64, visibility_ = 1 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.alias"() <{"alias_type" = i32, dso_local, "linkage" = #llvm.linkage<private>, "sym_name" = "a", thread_local_, "unnamed_addr" = 1 : i64, "visibility_" = 1 : i64}> ({
// CHECK: "llvm.mlir.addressof"() <{"global_name" = @g}> : () -> !llvm.ptr
// CHECK: "llvm.return"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> ()
