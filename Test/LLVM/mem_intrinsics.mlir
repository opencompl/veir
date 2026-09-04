// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i8, i64)>, linkage = #llvm.linkage<external>, sym_name = "copies"}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr, %byte: i8, %len: i64):
    "llvm.intr.memset"(%dst, %byte, %len) <{arg_attrs = [{llvm.align = 8 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = true}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memmove"(%dst, %src, %len) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.memset"({{.*}}) <{"arg_attrs" = [{"llvm.align" = 8 : i64, llvm.nonnull, llvm.noundef}, {}, {}], "isVolatile" = 0 : i1}> : (!llvm.ptr, i8, i64) -> ()
// CHECK: "llvm.intr.memcpy"({{.*}}) <{"isVolatile" = 1 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
// CHECK: "llvm.intr.memmove"({{.*}}) <{"isVolatile" = 0 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
