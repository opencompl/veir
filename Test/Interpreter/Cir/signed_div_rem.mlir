// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// -7 / 2 = -3 and -7 rem 2 = -1, combined as div * 10 + rem = -31.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "main"}> ({
    %a = "cir.const"() <{value = #cir.int<-7> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %b = "cir.const"() <{value = #cir.int<2> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %ten = "cir.const"() <{value = #cir.int<10> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %d = "cir.div"(%a, %b) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %r = "cir.rem"(%a, %b) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %d10 = "cir.mul"(%d, %ten) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %res = "cir.add"(%d10, %r) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%res) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffe1#32]
