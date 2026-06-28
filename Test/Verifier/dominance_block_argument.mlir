// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_AGREE

// Block arguments are subject to the same dominance rule as op results. %arg is
// an argument of ^a, but it is used in ^b, and ^a does not dominate ^b (^b is
// also reachable directly from ^entry).

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> i1, sym_name = "main"}> ({
  ^entry(%c : i1):
    "cf.cond_br"(%c, %c) [^a, ^b] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 0>}> : (i1, i1) -> ()
  ^a(%arg : i1):
    "cf.br"() [^b] : () -> ()
  ^b:
    "func.return"(%arg) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.return: operand 0 {{.*}} does not dominate its use
