// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The result type must match the vector element type.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (vector<4xi8>)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%v: vector<4xi8>):
    %r = "llvm.intr.vector.reduce.or"(%v) : (vector<4xi8>) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected result type to match vector element type
