// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 0 : i32}> ({
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = i32, linkage = #llvm.linkage<external>, sym_name = "a", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = i32, dso_local, linkage = #llvm.linkage<private>, sym_name = "b", thread_local_, unnamed_addr = 1 : i64, visibility_ = 1 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = i32, linkage = #llvm.linkage<external>, sym_name = "c", unnamed_addr = 2 : i64, visibility_ = 2 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @a}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "fa", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @f}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.alias"() <{"alias_type" = i32, "linkage" = #llvm.linkage<external>, "sym_name" = "a", "visibility_" = 0 : i64}> ({
// CHECK: "llvm.mlir.addressof"() <{"global_name" = @g}> : () -> !llvm.ptr
// CHECK: "llvm.return"(%{{[a-z0-9_]+}}) : (!llvm.ptr) -> ()
// CHECK: "llvm.mlir.alias"() <{"alias_type" = i32, dso_local, "linkage" = #llvm.linkage<private>, "sym_name" = "b", thread_local_, "unnamed_addr" = 1 : i64, "visibility_" = 1 : i64}> ({
// CHECK: "llvm.mlir.alias"() <{"alias_type" = i32, "linkage" = #llvm.linkage<external>, "sym_name" = "c", "unnamed_addr" = 2 : i64, "visibility_" = 2 : i64}> ({
// CHECK: "llvm.mlir.addressof"() <{"global_name" = @a}> : () -> !llvm.ptr
// CHECK: "llvm.mlir.alias"() <{"alias_type" = !llvm.func<!llvm.ptr ()>, "linkage" = #llvm.linkage<external>, "sym_name" = "fa", "visibility_" = 0 : i64}> ({
