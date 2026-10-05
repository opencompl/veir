// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A rank-zero vector is not an LLVM vector.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (vector<i8>)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%v: vector<i8>):
    %r = "llvm.intr.vector.reduce.or"(%v) : (vector<i8>) -> i8
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected a nonempty one-dimensional vector
