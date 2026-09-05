// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `llvm.intr.memset` takes a destination, a byte value and a length;
// `llvm.intr.memcpy` takes a destination, a source and a length. Both carry
// `isVolatile`, which MLIR materializes on parse, and both may carry the
// per-argument attributes clang knows -- alignment, dereferenceability -- in
// `arg_attrs`.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i8, i64)>, linkage = #llvm.linkage<external>, sym_name = "copies"}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr, %byte: i8, %len: i64):
    // The shape clang emits: what it knows about each argument, and not volatile.
    "llvm.intr.memset"(%dst, %byte, %len) <{arg_attrs = [{llvm.align = 8 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    // Volatile, and with nothing known about the arguments.
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = true}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    // `memmove` has the same shape as `memcpy`; only overlap tells them apart.
    "llvm.intr.memmove"(%dst, %src, %len) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.memset"({{.*}}) <{"arg_attrs" = [{"llvm.align" = 8 : i64, llvm.nonnull, llvm.noundef}, {}, {}], "isVolatile" = 0 : i1}> : (!llvm.ptr, i8, i64) -> ()
// CHECK: "llvm.intr.memcpy"({{.*}}) <{"isVolatile" = 1 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
// CHECK: "llvm.intr.memmove"({{.*}}) <{"isVolatile" = 0 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
