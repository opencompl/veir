// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// (7 + 5) * 3 = 36.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "main"}> ({
    %a = "cir.const"() <{value = #cir.int<7> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %b = "cir.const"() <{value = #cir.int<5> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %c = "cir.const"() <{value = #cir.int<3> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %s = "cir.add"(%a, %b) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %p = "cir.mul"(%s, %c) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%p) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000024#32]
