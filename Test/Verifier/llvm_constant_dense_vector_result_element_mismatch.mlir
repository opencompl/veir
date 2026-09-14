// RUN: not veir-opt %s 2>&1 | filecheck %s

// A vector result type is accepted for a dense constant, but its element type
// still has to be the one the attribute declares. `mlir-opt` does not check
// this, here or for an array result, so there is no MLIR run line.
"builtin.module"() ({
  %0 = "llvm.mlir.constant"() <{value = dense<1> : vector<2xi32>}> : () -> vector<2xi64>
}) : () -> ()

// CHECK: dense elements type 'i32' does not match vector element type 'i64'
