// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: VEIR_MLIR_SAME_VERDICT

// The use of %x is inside a graph region, where same-block operation order does
// not matter. But %x is defined in sibling CFG block ^b, and ^b does not
// dominate the graph-owning operation in ^a because ^a is reachable directly
// from ^entry.

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "main"}> ({
  ^entry(%c : i1):
    "cf.cond_br"(%c) [^b, ^a] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^b:
    %x = "arith.constant"() <{"value" = 5 : i32}> : () -> i32
    "cf.br"() [^a] : () -> ()
  ^a:
    "test.test"() ({
    ^inner:
      "test.test"(%x) : (i32) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: test.test: operand 0 {{.*}} does not dominate its use
