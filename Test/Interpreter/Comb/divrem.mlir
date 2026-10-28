// RUN: veir-interpret %s | filecheck %s

// Division and remainder are tested through the MLIR parser. The signed and unsigned forms are
// checked on the same bits and required to disagree, so an implementation defining all four in
// terms of the unsigned operations could not pass. A zero divisor is checked to yield poison,
// which is stricter than CIRCT leaving a zero divisor undefined.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8)}> ({
    // 200 unsigned, -56 signed.
    %a = "hw.constant"() <{ "value" = 200 : i8 }> : () -> i8
    %b = "hw.constant"() <{ "value" = 9 : i8 }> : () -> i8
    %zero = "hw.constant"() <{ "value" = 0 : i8 }> : () -> i8

    // 200 / 9 is 22; -56 / 9 truncates toward zero to -6.
    %divu = "comb.divu"(%a, %b) : (i8, i8) -> i8
    %divs = "comb.divs"(%a, %b) : (i8, i8) -> i8

    // 200 % 9 is 2; -56 % 9 is -2, taking its sign from the dividend.
    %modu = "comb.modu"(%a, %b) : (i8, i8) -> i8
    %mods = "comb.mods"(%a, %b) : (i8, i8) -> i8

    %div_zero = "comb.divu"(%a, %zero) : (i8, i8) -> i8
    %mod_zero = "comb.mods"(%a, %zero) : (i8, i8) -> i8

    "func.return"(%divu, %divs, %modu, %mods, %div_zero, %mod_zero) : (i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x16#8, 0xfa#8, 0x02#8, 0xfe#8, poison, poison]
