// RUN: veir-interpret %s | filecheck %s

// A carry can be wider than `i1`. The carry out is zero-extended, and the carry-in is read as `1`.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i32, i8, i32)}> ({
    %max = "llvm.mlir.constant"() <{ "value" = 255 : i8 }> : () -> i8
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %x, %x_carry = "gmir.g_uaddo"(%max, %one) : (i8, i8) -> (i8, i32)
    %y, %y_carry = "gmir.g_uadde"(%max, %zero, %x_carry) : (i8, i8, i32) -> (i8, i32)
    "func.return"(%x, %x_carry, %y, %y_carry) : (i8, i32, i8, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00#8, 0x00000001#32, 0x00#8, 0x00000001#32]
