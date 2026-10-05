// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Reduction takes exactly one vector.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (vector<4xi8>)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%v: vector<4xi8>):
    %r = "llvm.intr.vector.reduce.or"(%v, %v) : (vector<4xi8>, vector<4xi8>) -> i8
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected 1 operand(s)
