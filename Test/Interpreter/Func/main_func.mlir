// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %0 = "arith.constant"() <{ "value" = 14 : i32 }> : () -> i32
    %1 = "arith.constant"() <{ "value" = 28 : i32 }> : () -> i32
    %2 = "arith.addi"(%0, %1) : (i32, i32) -> i32
    "func.return"(%2) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32]
