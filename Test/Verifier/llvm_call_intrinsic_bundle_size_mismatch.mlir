// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    "llvm.call_intrinsic"(%p) <{intrin = "llvm.assume", op_bundle_sizes = array<i32: 2>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.call_intrinsic: op_bundle_sizes describes 2 operand(s), but operandSegmentSizes reserves 0
