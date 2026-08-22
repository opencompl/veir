// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_ROUNDTRIP

// Dominance is only meaningful inside blocks reachable from the region's entry,
// so operands of operations in unreachable blocks are not checked. ^bb1 has no
// predecessors, and its use of %x -- defined later, in ^bb2 -- is accepted.
// MLIR does the same: `verifyDominanceOfContainedRegions` guards the operand
// loop with `domInfo.isReachableFromEntry(&block)`.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
  ^bb0:
    "cf.br"() [^bb2] : () -> ()
  ^bb1:
    %y = "llvm.add"(%x, %x) : (i32, i32) -> i32
    "cf.br"() [^bb2] : () -> ()
  ^bb2:
    %x = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.add"
