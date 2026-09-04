// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// min(9, 4) = 4, max(4, 7) = 7, 7 xor 2 = 5.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "main"}> ({
    %a = "cir.const"() <{value = #cir.int<9> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %b = "cir.const"() <{value = #cir.int<4> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %c = "cir.const"() <{value = #cir.int<7> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %d = "cir.const"() <{value = #cir.int<2> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %mn = "cir.min"(%a, %b) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %mx = "cir.max"(%mn, %c) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %x = "cir.xor"(%mx, %d) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%x) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000005#32]
