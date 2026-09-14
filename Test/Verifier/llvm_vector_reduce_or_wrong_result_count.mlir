// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Reduction produces exactly one result.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (vector<4xi8>)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%v: vector<4xi8>):
    "llvm.intr.vector.reduce.or"(%v) : (vector<4xi8>) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected 1 result(s)
