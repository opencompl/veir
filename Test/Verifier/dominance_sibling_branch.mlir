// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_AGREE

// %x is defined in ^then and used in the sibling block ^else. Neither branch of
// the conditional dominates the other, so the use in ^else is not dominated by
// its definition.

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> i32, sym_name = "main"}> ({
  ^entry(%c : i1):
    "cf.cond_br"(%c) [^then, ^else] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^then:
    %x = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
    "func.return"(%x) : (i32) -> ()
  ^else:
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.return: operand 0 {{.*}} does not dominate its use
