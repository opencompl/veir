// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i8, i64)>, linkage = #llvm.linkage<external>, sym_name = "copies"}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr, %byte: i8, %len: i64):
    "llvm.intr.memset"(%dst, %byte, %len) <{arg_attrs = [{llvm.align = 8 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = true}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memmove"(%dst, %src, %len) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = false, access_groups = [], alias_scopes = [], noalias_scopes = [], tbaa = [#llvm.tbaa_tag<base_type = <id = "int", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, access_type = <id = "int", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, offset = 0>]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    // `res_attrs` says nothing on an operation with no results, but MLIR takes
    // it, so it round-trips rather than being refused.
    "llvm.intr.memset"(%dst, %byte, %len) <{isVolatile = false, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.memset"({{.*}}) <{"arg_attrs" = [{"llvm.align" = 8 : i64, llvm.nonnull, llvm.noundef}, {}, {}], "isVolatile" = 0 : i1}> : (!llvm.ptr, i8, i64) -> ()
// CHECK: "llvm.intr.memcpy"({{.*}}) <{"isVolatile" = 1 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
// CHECK: "llvm.intr.memmove"({{.*}}) <{"isVolatile" = 0 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
// CHECK: "llvm.intr.memcpy"({{.*}}) <{"access_groups" = [], "alias_scopes" = [], "isVolatile" = 0 : i1, "noalias_scopes" = [], "tbaa" = [#llvm.tbaa_tag<
// CHECK: "llvm.intr.memset"({{.*}}) <{"isVolatile" = 0 : i1, "res_attrs" = [{llvm.noundef}]}> : (!llvm.ptr, i8, i64) -> ()
