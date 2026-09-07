// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, i1)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr, %b: i1):
    "llvm.call_intrinsic"(%p, %b) <{intrin = "llvm.assume", op_bundle_sizes = array<i32: 1>, op_bundle_tags = [], operandSegmentSizes = array<i32: 1, 1>}> : (!llvm.ptr, i1) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.call_intrinsic: Expected 1 operand bundle tag(s), but got 0
