// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// The compiled code gives the same sums and differences, both when the low halves just carry or
// borrow and when they just fit. Values are written `hi:lo` with `i64` halves and `max` = 2^64 - 1.
//
//   0:max   + 1:1 = 2:0    carries
//   0:max-1 + 1:1 = 1:max  does not carry
//   2:0     - 1:1 = 0:max  borrows
//   2:1     - 1:1 = 1:0    does not borrow
//   0:max   + 0:1 = 1:0    carries into bit 64 of an `i65`, the only bit of `hi` that is checked

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)}> ({
    %max = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %below_max = "llvm.mlir.constant"() <{value = -2 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %y = "gmir.g_merge_values"(%one, %one) : (i64, i64) -> i128

    %x_carry = "gmir.g_merge_values"(%max, %zero) : (i64, i64) -> i128
    %add_carry = "gmir.g_add"(%x_carry, %y) : (i128, i128) -> i128
    %add_carry_lo, %add_carry_hi = "gmir.g_unmerge_values"(%add_carry) : (i128) -> (i64, i64)

    %x_no_carry = "gmir.g_merge_values"(%below_max, %zero) : (i64, i64) -> i128
    %add_no_carry = "gmir.g_add"(%x_no_carry, %y) : (i128, i128) -> i128
    %add_no_carry_lo, %add_no_carry_hi = "gmir.g_unmerge_values"(%add_no_carry) : (i128) -> (i64, i64)

    %x_borrow = "gmir.g_merge_values"(%zero, %two) : (i64, i64) -> i128
    %sub_borrow = "gmir.g_sub"(%x_borrow, %y) : (i128, i128) -> i128
    %sub_borrow_lo, %sub_borrow_hi = "gmir.g_unmerge_values"(%sub_borrow) : (i128) -> (i64, i64)

    %x_no_borrow = "gmir.g_merge_values"(%one, %two) : (i64, i64) -> i128
    %sub_no_borrow = "gmir.g_sub"(%x_no_borrow, %y) : (i128, i128) -> i128
    %sub_no_borrow_lo, %sub_no_borrow_hi = "gmir.g_unmerge_values"(%sub_no_borrow) : (i128) -> (i64, i64)

    %one_i128 = "gmir.g_merge_values"(%one, %zero) : (i64, i64) -> i128
    %x_i65 = "gmir.g_trunc"(%x_carry) : (i128) -> i65
    %y_i65 = "gmir.g_trunc"(%one_i128) : (i128) -> i65
    %add_i65 = "gmir.g_add"(%x_i65, %y_i65) : (i65, i65) -> i65
    %add_i65_wide = "gmir.g_anyext"(%add_i65) : (i65) -> i128
    %add_i65_lo, %add_i65_hi = "gmir.g_unmerge_values"(%add_i65_wide) : (i128) -> (i64, i64)
    %add_i65_bit64 = "gmir.g_and"(%add_i65_hi, %one) : (i64, i64) -> i64

    "func.return"(%add_carry_hi, %add_carry_lo, %add_no_carry_hi, %add_no_carry_lo, %sub_borrow_hi, %sub_borrow_lo, %sub_no_borrow_hi, %sub_no_borrow_lo, %add_i65_bit64, %add_i65_lo) : (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000002#64, 0x0000000000000000#64, 0x0000000000000001#64, 0xffffffffffffffff#64, 0x0000000000000000#64, 0xffffffffffffffff#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000000#64]
// CHECK: Program output: #[0x0000000000000002#64, 0x0000000000000000#64, 0x0000000000000001#64, 0xffffffffffffffff#64, 0x0000000000000000#64, 0xffffffffffffffff#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000000#64]
