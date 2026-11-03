// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i1) -> ()}> ({
  ^bb0(%c : i1):
    %k = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "cf.cond_br"(%c, %k) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb1(%a : i32):
    "cf.br"() [^bb3] : () -> ()
  ^bb2:
    %y = "llvm.add"(%a, %a) : (i32, i32) -> i32
    "cf.br"() [^bb3] : () -> ()
  ^bb3:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.add: operand #0 does not dominate this use
