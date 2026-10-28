// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: veir-opt %s -p=riscv | filecheck %s --check-prefix=ISEL

// Each `llvm.cond_br` on an `llvm.icmp` sets one bit when its branch is taken: bits 0-9 compare
// -1 and 1, and bits 10-19 compare 5 with itself, for the predicates eq, ne, slt, sle, sgt, sge,
// ult, ule, ugt and uge in turn.
// The operands are block arguments, so that no compare is selected as one against an immediate,
// and every compare is folded into a compare-and-branch.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^entry():
      %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
      %m1c = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
      %onec = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
      %fivec = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
      "llvm.br"(%zero, %m1c, %onec, %fivec) [^b0] : (i64, i64, i64, i64) -> ()
    ^b0(%acc0 : i64, %m1 : i64, %one : i64, %five : i64):
      %c0 = "llvm.icmp"(%m1, %one) <{predicate = 0 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c0, %acc0, %acc0) [^t0, ^b1] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t0(%u0 : i64):
      %bit0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
      %s0 = "llvm.or"(%u0, %bit0) : (i64, i64) -> i64
      "llvm.br"(%s0) [^b1] : (i64) -> ()
    ^b1(%acc1 : i64):
      %c1 = "llvm.icmp"(%m1, %one) <{predicate = 1 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c1, %acc1, %acc1) [^t1, ^b2] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t1(%u1 : i64):
      %bit1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
      %s1 = "llvm.or"(%u1, %bit1) : (i64, i64) -> i64
      "llvm.br"(%s1) [^b2] : (i64) -> ()
    ^b2(%acc2 : i64):
      %c2 = "llvm.icmp"(%m1, %one) <{predicate = 2 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c2, %acc2, %acc2) [^t2, ^b3] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t2(%u2 : i64):
      %bit2 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
      %s2 = "llvm.or"(%u2, %bit2) : (i64, i64) -> i64
      "llvm.br"(%s2) [^b3] : (i64) -> ()
    ^b3(%acc3 : i64):
      %c3 = "llvm.icmp"(%m1, %one) <{predicate = 3 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c3, %acc3, %acc3) [^t3, ^b4] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t3(%u3 : i64):
      %bit3 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
      %s3 = "llvm.or"(%u3, %bit3) : (i64, i64) -> i64
      "llvm.br"(%s3) [^b4] : (i64) -> ()
    ^b4(%acc4 : i64):
      %c4 = "llvm.icmp"(%m1, %one) <{predicate = 4 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c4, %acc4, %acc4) [^t4, ^b5] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t4(%u4 : i64):
      %bit4 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
      %s4 = "llvm.or"(%u4, %bit4) : (i64, i64) -> i64
      "llvm.br"(%s4) [^b5] : (i64) -> ()
    ^b5(%acc5 : i64):
      %c5 = "llvm.icmp"(%m1, %one) <{predicate = 5 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c5, %acc5, %acc5) [^t5, ^b6] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t5(%u5 : i64):
      %bit5 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
      %s5 = "llvm.or"(%u5, %bit5) : (i64, i64) -> i64
      "llvm.br"(%s5) [^b6] : (i64) -> ()
    ^b6(%acc6 : i64):
      %c6 = "llvm.icmp"(%m1, %one) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c6, %acc6, %acc6) [^t6, ^b7] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t6(%u6 : i64):
      %bit6 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
      %s6 = "llvm.or"(%u6, %bit6) : (i64, i64) -> i64
      "llvm.br"(%s6) [^b7] : (i64) -> ()
    ^b7(%acc7 : i64):
      %c7 = "llvm.icmp"(%m1, %one) <{predicate = 7 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c7, %acc7, %acc7) [^t7, ^b8] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t7(%u7 : i64):
      %bit7 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
      %s7 = "llvm.or"(%u7, %bit7) : (i64, i64) -> i64
      "llvm.br"(%s7) [^b8] : (i64) -> ()
    ^b8(%acc8 : i64):
      %c8 = "llvm.icmp"(%m1, %one) <{predicate = 8 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c8, %acc8, %acc8) [^t8, ^b9] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t8(%u8 : i64):
      %bit8 = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
      %s8 = "llvm.or"(%u8, %bit8) : (i64, i64) -> i64
      "llvm.br"(%s8) [^b9] : (i64) -> ()
    ^b9(%acc9 : i64):
      %c9 = "llvm.icmp"(%m1, %one) <{predicate = 9 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c9, %acc9, %acc9) [^t9, ^b10] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t9(%u9 : i64):
      %bit9 = "llvm.mlir.constant"() <{value = 512 : i64}> : () -> i64
      %s9 = "llvm.or"(%u9, %bit9) : (i64, i64) -> i64
      "llvm.br"(%s9) [^b10] : (i64) -> ()
    ^b10(%acc10 : i64):
      %c10 = "llvm.icmp"(%five, %five) <{predicate = 0 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c10, %acc10, %acc10) [^t10, ^b11] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t10(%u10 : i64):
      %bit10 = "llvm.mlir.constant"() <{value = 1024 : i64}> : () -> i64
      %s10 = "llvm.or"(%u10, %bit10) : (i64, i64) -> i64
      "llvm.br"(%s10) [^b11] : (i64) -> ()
    ^b11(%acc11 : i64):
      %c11 = "llvm.icmp"(%five, %five) <{predicate = 1 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c11, %acc11, %acc11) [^t11, ^b12] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t11(%u11 : i64):
      %bit11 = "llvm.mlir.constant"() <{value = 2048 : i64}> : () -> i64
      %s11 = "llvm.or"(%u11, %bit11) : (i64, i64) -> i64
      "llvm.br"(%s11) [^b12] : (i64) -> ()
    ^b12(%acc12 : i64):
      %c12 = "llvm.icmp"(%five, %five) <{predicate = 2 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c12, %acc12, %acc12) [^t12, ^b13] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t12(%u12 : i64):
      %bit12 = "llvm.mlir.constant"() <{value = 4096 : i64}> : () -> i64
      %s12 = "llvm.or"(%u12, %bit12) : (i64, i64) -> i64
      "llvm.br"(%s12) [^b13] : (i64) -> ()
    ^b13(%acc13 : i64):
      %c13 = "llvm.icmp"(%five, %five) <{predicate = 3 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c13, %acc13, %acc13) [^t13, ^b14] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t13(%u13 : i64):
      %bit13 = "llvm.mlir.constant"() <{value = 8192 : i64}> : () -> i64
      %s13 = "llvm.or"(%u13, %bit13) : (i64, i64) -> i64
      "llvm.br"(%s13) [^b14] : (i64) -> ()
    ^b14(%acc14 : i64):
      %c14 = "llvm.icmp"(%five, %five) <{predicate = 4 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c14, %acc14, %acc14) [^t14, ^b15] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t14(%u14 : i64):
      %bit14 = "llvm.mlir.constant"() <{value = 16384 : i64}> : () -> i64
      %s14 = "llvm.or"(%u14, %bit14) : (i64, i64) -> i64
      "llvm.br"(%s14) [^b15] : (i64) -> ()
    ^b15(%acc15 : i64):
      %c15 = "llvm.icmp"(%five, %five) <{predicate = 5 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c15, %acc15, %acc15) [^t15, ^b16] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t15(%u15 : i64):
      %bit15 = "llvm.mlir.constant"() <{value = 32768 : i64}> : () -> i64
      %s15 = "llvm.or"(%u15, %bit15) : (i64, i64) -> i64
      "llvm.br"(%s15) [^b16] : (i64) -> ()
    ^b16(%acc16 : i64):
      %c16 = "llvm.icmp"(%five, %five) <{predicate = 6 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c16, %acc16, %acc16) [^t16, ^b17] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t16(%u16 : i64):
      %bit16 = "llvm.mlir.constant"() <{value = 65536 : i64}> : () -> i64
      %s16 = "llvm.or"(%u16, %bit16) : (i64, i64) -> i64
      "llvm.br"(%s16) [^b17] : (i64) -> ()
    ^b17(%acc17 : i64):
      %c17 = "llvm.icmp"(%five, %five) <{predicate = 7 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c17, %acc17, %acc17) [^t17, ^b18] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t17(%u17 : i64):
      %bit17 = "llvm.mlir.constant"() <{value = 131072 : i64}> : () -> i64
      %s17 = "llvm.or"(%u17, %bit17) : (i64, i64) -> i64
      "llvm.br"(%s17) [^b18] : (i64) -> ()
    ^b18(%acc18 : i64):
      %c18 = "llvm.icmp"(%five, %five) <{predicate = 8 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c18, %acc18, %acc18) [^t18, ^b19] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t18(%u18 : i64):
      %bit18 = "llvm.mlir.constant"() <{value = 262144 : i64}> : () -> i64
      %s18 = "llvm.or"(%u18, %bit18) : (i64, i64) -> i64
      "llvm.br"(%s18) [^b19] : (i64) -> ()
    ^b19(%acc19 : i64):
      %c19 = "llvm.icmp"(%five, %five) <{predicate = 9 : i64}> : (i64, i64) -> i1
      "llvm.cond_br"(%c19, %acc19, %acc19) [^t19, ^b20] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
    ^t19(%u19 : i64):
      %bit19 = "llvm.mlir.constant"() <{value = 524288 : i64}> : () -> i64
      %s19 = "llvm.or"(%u19, %bit19) : (i64, i64) -> i64
      "llvm.br"(%s19) [^b20] : (i64) -> ()
    ^b20(%res : i64):
      "llvm.return"(%res) : (i64) -> ()

  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000000000aa70e#64]
// CHECK: Program output: #[0x00000000000aa70e#64]

// ISEL-NOT: riscv_cf.bnez
// ISEL-NOT: riscv.slt
// ISEL-NOT: riscv.xor
