// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// A dense elements constant may have a vector result type as well as an array
// one: `dense<1> : vector<2xi32>` against a `vector<2xi32>` result is what
// clang emits for a vectorized splat, and it is the shape the sqlite3 corpus
// reaches for most often.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "splats"}> ({
    // A splat, written as a single element.
    %a = "llvm.mlir.constant"() <{value = dense<1> : vector<2xi32>}> : () -> vector<2xi32>
    // One element per lane, and a narrower element type.
    %b = "llvm.mlir.constant"() <{value = dense<[1, 2, 3, 4]> : vector<4xi16>}> : () -> vector<4xi16>
    // The array form the verifier already accepted, for contrast.
    %c = "llvm.mlir.constant"() <{value = dense<[104, 105]> : tensor<2xi8>}> : () -> !llvm.array<2 x i8>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.constant"() <{"value" = dense<1> : vector<2xi32>}> : () -> vector<2xi32>
// CHECK: "llvm.mlir.constant"() <{"value" = dense<[1, 2, 3, 4]> : vector<4xi16>}> : () -> vector<4xi16>
// CHECK: "llvm.mlir.constant"() <{"value" = dense<[104, 105]> : tensor<2xi8>}> : () -> !llvm.array<2 x i8>
