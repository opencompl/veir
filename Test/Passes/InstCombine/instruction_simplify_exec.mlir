// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=instcombine > %t
// RUN: veir-interpret %t | filecheck %s
// RUN: veir-opt %t --print-op-generic > %t.canonical
// RUN: veir-opt %t --print-op-generic -p=instcombine > %t.second
// RUN: diff %t.canonical %t.second
// Constants exercise i1 normalization, odd widths, casts, poison flags, and
// boundary counterexamples for source rules deliberately left unported.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8, i8, i16, i3, i8, i9, i64, i1, i8, i8, i8, i8, i3, i8)}> ({
    // nsw_mul_neg_one
    %c0_arg0 = "llvm.mlir.constant"() <{value = 5 : i8}> : () -> i8
    %c0_v0 = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i8
    %c0_v1 = "llvm.mul"(%c0_arg0, %c0_v0) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    // or_not_and3_contains
    %c1_arg0 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %c1_arg1 = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %c1_arg2 = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %c1_v0 = "llvm.and"(%c1_arg0, %c1_arg1) : (i8, i8) -> i8
    %c1_v1 = "llvm.and"(%c1_v0, %c1_arg2) : (i8, i8) -> i8
    %c1_v2 = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i8
    %c1_v3 = "llvm.xor"(%c1_v1, %c1_v2) : (i8, i8) -> i8
    %c1_v4 = "llvm.or"(%c1_arg0, %c1_v3) : (i8, i8) -> i8
    // select_sgt_nsw_add_const_to_smax_nsw_add
    %c2_arg0 = "llvm.mlir.constant"() <{value = 8 : i8}> : () -> i8
    %c2_v0 = "llvm.mlir.constant"() <{value = 10 : i8}> : () -> i8
    %c2_v1 = "llvm.icmp"(%c2_arg0, %c2_v0) <{predicate = 4 : i64}> : (i8, i8) -> i1
    %c2_v2 = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %c2_v3 = "llvm.add"(%c2_arg0, %c2_v2) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %c2_v4 = "llvm.mlir.constant"() <{value = 13 : i8}> : () -> i8
    %c2_v5 = "llvm.select"(%c2_v1, %c2_v3, %c2_v4) : (i1, i8, i8) -> i8
    // uadd_sat_nested_constants_to_max
    %c3_arg0 = "llvm.mlir.constant"() <{value = 150 : i8}> : () -> i8
    %c3_v0 = "llvm.mlir.constant"() <{value = 200 : i8}> : () -> i8
    %c3_v1 = "llvm.intr.uadd.sat"(%c3_arg0, %c3_v0) : (i8, i8) -> i8
    %c3_v2 = "llvm.mlir.constant"() <{value = 100 : i8}> : () -> i8
    %c3_v3 = "llvm.intr.uadd.sat"(%c3_v1, %c3_v2) : (i8, i8) -> i8
    // usub_sat_nested_constants
    %c4_arg0 = "llvm.mlir.constant"() <{value = 12 : i8}> : () -> i8
    %c4_v0 = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %c4_v1 = "llvm.intr.usub.sat"(%c4_arg0, %c4_v0) : (i8, i8) -> i8
    %c4_v2 = "llvm.mlir.constant"() <{value = 4 : i8}> : () -> i8
    %c4_v3 = "llvm.intr.usub.sat"(%c4_v1, %c4_v2) : (i8, i8) -> i8
    // ctlz_bitreverse
    %c5_arg0 = "llvm.mlir.constant"() <{value = 16 : i8}> : () -> i8
    %c5_v0 = "llvm.intr.bitreverse"(%c5_arg0) : (i8) -> i8
    %c5_v1 = "llvm.intr.ctlz"(%c5_v0) <{is_zero_poison = false}> : (i8) -> i8
    // umin_cttz_cttz
    %c6_arg0 = "llvm.mlir.constant"() <{value = 16 : i8}> : () -> i8
    %c6_arg1 = "llvm.mlir.constant"() <{value = 128 : i8}> : () -> i8
    %c6_v0 = "llvm.intr.cttz"(%c6_arg0) <{is_zero_poison = false}> : (i8) -> i8
    %c6_v1 = "llvm.intr.cttz"(%c6_arg1) <{is_zero_poison = true}> : (i8) -> i8
    %c6_v2 = "llvm.intr.umin"(%c6_v0, %c6_v1) : (i8, i8) -> i8
    // or_bswap_const_distribute
    %c7_arg0 = "llvm.mlir.constant"() <{value = 4660 : i16}> : () -> i16
    %c7_v0 = "llvm.intr.bswap"(%c7_arg0) : (i16) -> i16
    %c7_v1 = "llvm.mlir.constant"() <{value = 255 : i16}> : () -> i16
    %c7_v2 = "llvm.or"(%c7_v0, %c7_v1) : (i16, i16) -> i16
    // fshl_zero_lo_to_shl
    %c8_arg0 = "llvm.mlir.constant"() <{value = 3 : i3}> : () -> i3
    %c8_v0 = "llvm.mlir.constant"() <{value = 0 : i3}> : () -> i3
    %c8_v1 = "llvm.mlir.constant"() <{value = 2 : i3}> : () -> i3
    %c8_v2 = "llvm.intr.fshl"(%c8_arg0, %c8_v0, %c8_v1) : (i3, i3, i3) -> i3
    // bitreverse_zext_i1_to_select
    %c9_arg0 = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %c9_v0 = "llvm.zext"(%c9_arg0) : (i1) -> i8
    %c9_v1 = "llvm.intr.bitreverse"(%c9_v0) : (i8) -> i8
    // cttz_zext_zero_poison_narrow
    %c10_arg0 = "llvm.mlir.constant"() <{value = 16 : i8}> : () -> i8
    %c10_v0 = "llvm.zext"(%c10_arg0) : (i8) -> i9
    %c10_v1 = "llvm.intr.cttz"(%c10_v0) <{is_zero_poison = true}> : (i9) -> i9
    // ctpop_lshr_allones
    %c11_arg0 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %c11_v0 = "llvm.mlir.constant"() <{value = 18446744073709551615 : i64}> : () -> i64
    %c11_v1 = "llvm.lshr"(%c11_v0, %c11_arg0) : (i64, i64) -> i64
    %c11_v2 = "llvm.intr.ctpop"(%c11_v1) : (i64) -> i64
    // i_cttz_with_poison_i1_zero_defined
    %c12_arg0 = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    %c12_v0 = "llvm.intr.cttz"(%c12_arg0) <{is_zero_poison = false}> : (i1) -> i1
    // smax_nsw_neg_to_neg_smin
    %c13_arg0 = "llvm.mlir.constant"() <{value = 5 : i8}> : () -> i8
    %c13_arg1 = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %c13_v0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c13_v1 = "llvm.sub"(%c13_v0, %c13_arg0) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %c13_v2 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c13_v3 = "llvm.sub"(%c13_v2, %c13_arg1) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %c13_v4 = "llvm.intr.smax"(%c13_v1, %c13_v3) : (i8, i8) -> i8
    // abs_plain_not_zext
    %c14_arg0 = "llvm.mlir.constant"() <{value = 127 : i7}> : () -> i7
    %c14_v0 = "llvm.zext"(%c14_arg0) : (i7) -> i8
    %c14_v1 = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i8
    %c14_v2 = "llvm.xor"(%c14_v0, %c14_v1) : (i8, i8) -> i8
    %c14_v3 = "llvm.intr.abs"(%c14_v2) <{is_int_min_poison = false}> : (i8) -> i8
    // cttz_exact_lshr_const
    %c15_arg0 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %c15_v0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c15_v1 = "llvm.lshr"(%c15_v0, %c15_arg0) <{isExact}> : (i8, i8) -> i8
    %c15_v2 = "llvm.intr.cttz"(%c15_v1) <{is_zero_poison = false}> : (i8) -> i8
    // select_ult_const_add_to_decremented_umax_add
    %c16_arg0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c16_v0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c16_v1 = "llvm.icmp"(%c16_arg0, %c16_v0) <{predicate = 6 : i64}> : (i8, i8) -> i1
    %c16_v2 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c16_v3 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %c16_v4 = "llvm.add"(%c16_arg0, %c16_v3) : (i8, i8) -> i8
    %c16_v5 = "llvm.select"(%c16_v1, %c16_v2, %c16_v4) : (i1, i8, i8) -> i8
    // fshr_self_const_to_fshl
    %c17_arg0 = "llvm.mlir.constant"() <{value = 1 : i3}> : () -> i3
    %c17_v0 = "llvm.mlir.constant"() <{value = 4 : i3}> : () -> i3
    %c17_v1 = "llvm.intr.fshr"(%c17_arg0, %c17_arg0, %c17_v0) : (i3, i3, i3) -> i3
    // fshl_rotate_exact_high_mask_to_lshr
    %c18_arg0 = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %c18_v0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c18_v1 = "llvm.and"(%c18_arg0, %c18_v0) : (i8, i8) -> i8
    %c18_v2 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c18_v3 = "llvm.intr.fshl"(%c18_v1, %c18_v1, %c18_v2) : (i8, i8, i8) -> i8
    "func.return"(%c0_v1, %c1_v4, %c2_v5, %c3_v3, %c4_v3, %c5_v1, %c6_v2, %c7_v2, %c8_v2, %c9_v1, %c10_v1, %c11_v2, %c12_v0, %c13_v4, %c14_v3, %c15_v2, %c16_v5, %c17_v1, %c18_v3) : (i8, i8, i8, i8, i8, i8, i8, i16, i3, i8, i9, i64, i1, i8, i8, i8, i8, i3, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfb#8, 0xff#8, 0x0d#8, 0xff#8, 0x05#8, 0x04#8, 0x04#8, 0x34ff#16, 0x4#3, 0x80#8, 0x004#9, 0x0000000000000038#64, 0x1#1, 0xfb#8, 0x80#8, 0x08#8, 0x01#8, 0x4#3, 0x00#8]
