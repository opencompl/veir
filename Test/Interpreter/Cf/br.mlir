// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  ^1():
    %x1 = "arith.constant"() <{"value" = 8 : i32}> : () -> i32
    %x2 = "arith.constant"() <{"value" = 11 : i32}> : () -> i32
    "cf.br"(%x1, %x2) [^2] : (i32, i32) -> ()
  ^2(%y1 : i32, %y2 : i32):
    "func.return"(%y2) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000b#32]
