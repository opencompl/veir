// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// sum of 1..10 through a flat loop = 55.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "main"}> ({
    %zero = "cir.const"() <{value = #cir.int<0> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %one = "cir.const"() <{value = #cir.int<1> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %ten = "cir.const"() <{value = #cir.int<10> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    "cir.br"(%zero, %one)[^loop] : (!cir.int<s, 32>, !cir.int<s, 32>) -> ()
  ^loop(%acc : !cir.int<s, 32>, %i : !cir.int<s, 32>):
    %acc2 = "cir.add"(%acc, %i) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %i2 = "cir.add"(%i, %one) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %more = "cir.cmp"(%i2, %ten) <{kind = 1 : i32}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.bool
    "cir.brcond"(%more, %acc2, %i2, %acc2)[^loop, ^done] <{operandSegmentSizes = array<i32: 1, 2, 1>}> : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>, !cir.int<s, 32>) -> ()
  ^done(%r : !cir.int<s, 32>):
    "cir.return"(%r) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000037#32]
