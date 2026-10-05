// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Bundle tags are the bundle names, so they have to be strings.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1, !llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%c: i1, %p: !llvm.ptr):
    "llvm.intr.assume"(%c, %p) <{op_bundle_sizes = array<i32: 1>, op_bundle_tags = [1 : i32]}> : (i1, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.assume: Expected operand bundle tags to be string attributes
