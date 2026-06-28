// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_AGREE

// The block argument %arg is only available along the path through ^b. Hiding
// its use inside a nested graph region in sibling block ^a must not bypass the
// enclosing SSACFG dominance requirement.

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "main"}> ({
  ^entry(%c : i1):
    %v = "arith.constant"() <{"value" = 5 : i32}> : () -> i32
    "cf.cond_br"(%c, %v) [^b, ^a] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^b(%arg : i32):
    "cf.br"() [^a] : () -> ()
  ^a:
    "test.test"() ({
    ^inner:
      "test.test"(%arg) : (i32) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: test.test: operand 0 {{.*}} does not dominate its use
