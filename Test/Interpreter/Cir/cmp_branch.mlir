// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// 3 < 5 is true, so the true branch returns 3 + 100 = 103.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "main"}> ({
    %a = "cir.const"() <{value = #cir.int<3> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %b = "cir.const"() <{value = #cir.int<5> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %k = "cir.const"() <{value = #cir.int<100> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %lt = "cir.cmp"(%a, %b) <{kind = 0 : i32}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.bool
    "cir.brcond"(%lt, %a, %b)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>) -> ()
  ^bb1(%t : !cir.int<s, 32>):
    %x = "cir.add"(%t, %k) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.br"(%x)[^bb3] : (!cir.int<s, 32>) -> ()
  ^bb2(%f : !cir.int<s, 32>):
    "cir.br"(%f)[^bb3] : (!cir.int<s, 32>) -> ()
  ^bb3(%r : !cir.int<s, 32>):
    "cir.return"(%r) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000067#32]
