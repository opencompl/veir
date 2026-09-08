// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Each bundle is named by a tag, so one bundle needs exactly one tag.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1, !llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%c: i1, %p: !llvm.ptr):
    "llvm.intr.assume"(%c, %p) <{op_bundle_sizes = array<i32: 1>}> : (i1, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.assume: Expected 1 operand bundle tag(s), but got 0
