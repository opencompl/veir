// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// MLIR does not check `arg_attrs` or `res_attrs` against the operand or result
// count, so neither does VeIR.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "lengths"}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr, %len: i64):
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = false, arg_attrs = [{}, {}]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memmove"(%dst, %src, %len) <{isVolatile = false, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.memcpy"({{.*}}) <{"arg_attrs" = [{}, {}], "isVolatile" = 0 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
// CHECK: "llvm.intr.memmove"({{.*}}) <{"isVolatile" = 0 : i1, "res_attrs" = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
