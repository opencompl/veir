// RUN: veir-interpret %s | filecheck %s

// Only the carry-in makes 255 + 0 wrap around in `i8`, so it carries, while 254 + 0 + 1 just fits.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1)}> ({
    %max = "llvm.mlir.constant"() <{ "value" = 255 : i8 }> : () -> i8
    %below_max = "llvm.mlir.constant"() <{ "value" = 254 : i8 }> : () -> i8
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %carry = "llvm.mlir.constant"() <{ "value" = true }> : () -> i1
    %x, %x_carry = "gmir.g_uadde"(%max, %zero, %carry) : (i8, i8, i1) -> (i8, i1)
    %y, %y_carry = "gmir.g_uadde"(%below_max, %zero, %carry) : (i8, i8, i1) -> (i8, i1)
    "func.return"(%x, %x_carry, %y, %y_carry) : (i8, i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00#8, 0x1#1, 0xff#8, 0x0#1]
