// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// Reduce an integer vector to the bitwise OR of its elements. SQLite uses
// vector<4xi8>; the element width and number of lanes may vary independently.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (vector<4xi8>, vector<2xi32>, vector<8xi1>)>, linkage = #llvm.linkage<external>, sym_name = "reduce"}> ({
  ^bb0(%bytes: vector<4xi8>, %words: vector<2xi32>, %bits: vector<8xi1>):
    %a = "llvm.intr.vector.reduce.or"(%bytes) : (vector<4xi8>) -> i8
    %b = "llvm.intr.vector.reduce.or"(%words) : (vector<2xi32>) -> i32
    %c = "llvm.intr.vector.reduce.or"(%bits) : (vector<8xi1>) -> i1
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.vector.reduce.or"(%{{[a-z0-9_]+}}) : (vector<4xi8>) -> i8
// CHECK: "llvm.intr.vector.reduce.or"(%{{[a-z0-9_]+}}) : (vector<2xi32>) -> i32
// CHECK: "llvm.intr.vector.reduce.or"(%{{[a-z0-9_]+}}) : (vector<8xi1>) -> i1
