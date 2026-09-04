// RUN: not veir-opt %s 2>&1 | filecheck %s
//
// A deliberate divergence, so no MLIR_INVALID here: mlir-opt accepts this,
// because it does not check `llvm.mlir.zero` against its zeroable-type
// constraint when parsing the generic form. There is no zero of void, so veir
// rejects it. Every type that does have a zero -- integers, pointers, floats,
// aggregates -- is accepted; see mlir_zero.mlir and mlir_zero_aggregate.mlir.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
    %bad = "llvm.mlir.zero"() : () -> !llvm.void
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.zero: Expected result to have a type with a zero value
