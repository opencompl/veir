// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, i1)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr, %b: i1):
    "llvm.call_intrinsic"(%p) <{intrin = "llvm.assume", op_bundle_sizes = array<i32>, operandSegmentSizes = array<i64: 1, 0>}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.call_intrinsic: Expected 'operandSegmentSizes' to be an i32 dense array attribute
