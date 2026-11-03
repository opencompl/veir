// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// 300 narrowed to s8 is 44, widened back to s32 is 44; int_to_bool then bool_to_int of 44 is 1; select on that picks 44 + 1 = 45; minus and not give -(45) and ~(-45) = 44.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "main"}> ({
    %big = "cir.const"() <{value = #cir.int<300> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %one = "cir.const"() <{value = #cir.int<1> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %narrow = "cir.cast"(%big) <{kind = 27 : i32}> : (!cir.int<s, 32>) -> !cir.int<s, 8>
    %wide = "cir.cast"(%narrow) <{kind = 27 : i32}> : (!cir.int<s, 8>) -> !cir.int<s, 32>
    %b = "cir.cast"(%wide) <{kind = 28 : i32}> : (!cir.int<s, 32>) -> !cir.bool
    %bi = "cir.cast"(%b) <{kind = 38 : i32}> : (!cir.bool) -> !cir.int<s, 32>
    %sum = "cir.add"(%wide, %bi) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %sel = "cir.select"(%b, %sum, %one) : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %neg = "cir.minus"(%sel) <{no_signed_wrap = false}> : (!cir.int<s, 32>) -> !cir.int<s, 32>
    %not = "cir.not"(%neg) : (!cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%not) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002c#32]
