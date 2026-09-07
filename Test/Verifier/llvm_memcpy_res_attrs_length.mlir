// RUN: not veir-opt %s 2>&1 | filecheck %s

// One entry per result, and a memory intrinsic has none. `mlir-opt` accepts
// any length, so there is no MLIR run line.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr, %len: i64):
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = false, res_attrs = [{llvm.noundef}]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.memcpy: Expected 0 'res_attrs' entries, but got 1
