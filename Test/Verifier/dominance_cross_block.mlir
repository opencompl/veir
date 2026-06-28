// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_AGREE

// %x is defined in ^a but used in ^b. ^a does not dominate ^b, because ^b is
// also reachable directly from ^entry, so this violates SSA dominance even
// though every name is assigned exactly once and every use is defined.

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> i32, sym_name = "main"}> ({
  ^entry(%c : i1):
    "cf.cond_br"(%c) [^a, ^b] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^a:
    %x = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "cf.br"() [^b] : () -> ()
  ^b:
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.return: operand 0 {{.*}} does not dominate its use
