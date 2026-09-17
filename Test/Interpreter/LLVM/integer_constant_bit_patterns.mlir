// RUN: veir-interpret %s | filecheck %s

// Cover a non-power-of-two width, unsigned sign-bit and hexadecimal spellings,
// and a literal larger than a host integer. Existing interpreter tests cover
// i1 true/false, signed i8 boundaries, and decimal 255 : i8.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i3, i8, i8, i128)}> ({
    %oddWidth = "llvm.mlir.constant"() <{value = 7 : i3}> : () -> i3
    %signBit = "llvm.mlir.constant"() <{value = 128 : i8}> : () -> i8
    %hex = "llvm.mlir.constant"() <{value = 0xff : i8}> : () -> i8
    %wide = "llvm.mlir.constant"() <{value = 340282366920938463463374607431768211455 : i128}> : () -> i128
    "func.return"(%oddWidth, %signBit, %hex, %wide) : (i3, i8, i8, i128) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x7#3, 0x80#8, 0xff#8, 0xffffffffffffffffffffffffffffffff#128]
