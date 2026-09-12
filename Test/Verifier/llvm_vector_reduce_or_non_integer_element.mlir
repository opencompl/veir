// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Bitwise OR reduction requires integer elements.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (vector<4xf32>)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%v: vector<4xf32>):
    %r = "llvm.intr.vector.reduce.or"(%v) : (vector<4xf32>) -> f32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected vector elements to have integer type
