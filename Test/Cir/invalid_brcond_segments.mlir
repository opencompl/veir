// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.brcond: true operand segment expected operand count 0, got 1
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<()>, sym_name = "f"}> ({
    %0 = "cir.const"() <{value = #cir.bool<true> : !cir.bool}> : () -> !cir.bool
    "cir.brcond"(%0, %0)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (!cir.bool, !cir.bool) -> ()
  ^bb1:
    "cir.return"() : () -> ()
  ^bb2:
    "cir.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
