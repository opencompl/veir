// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_AGREE

// builtin.module is a registered op with a graph region, so its region may have
// at most one block. (Unregistered ops and the test dialect are exempt and may
// use multi-block graph regions.)

"builtin.module"() ({
^bb0:
  "func.func"() <{function_type = () -> (), sym_name = "a"}> ({ ^e0: "func.return"() : () -> () }) : () -> ()
^bb1:
  "func.func"() <{function_type = () -> (), sym_name = "b"}> ({ ^e1: "func.return"() : () -> () }) : () -> ()
}) : () -> ()

// CHECK: expects graph region 0 to have 0 or 1 blocks
