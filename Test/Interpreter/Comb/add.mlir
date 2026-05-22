// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %c3 = "hw.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %c5 = "hw.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %c10 = "hw.constant"() <{ "value" = 10 : i8 }> : () -> i8
    %x = "comb.add"(%c3) : (i8) -> i8
    %y = "comb.add"(%c3, %c5) : (i8, i8) -> i8
    %z = "comb.add"(%c3, %c5, %c10) : (i8, i8, i8) -> i8

    %c255 = "hw.constant"() <{ "value" = 255 : i8 }> : () -> i8
    %nuw_nsw = "llvm.add"(%c255, %c5) <{nuw, nsw}> : (i8, i8) -> i8
    %poison = "comb.add"(%nuw_nsw, %c5) : (i8, i8) -> i8
    "func.return"(%x, %y, %z, %poison) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x03#8, 0x08#8, 0x12#8, poison]
