// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// `sextw (op …) -> op …` when `op` already returns a sign-extended value. Each
// function covers one group of instructions, in the order of `Combine.lean`.

"builtin.module"() ({

// Loads.
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "loads"}> ({
  ^bb0(%x: !riscv.reg):
    %0 = "riscv.lw"(%x) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %1 = "riscv.lh"(%x) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.lb"(%x) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.lhu"(%x) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %4 = "riscv.lbu"(%x) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    %s4 = "riscv.sextw"(%4) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3, %s4) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
// CHECK-LABEL: func.func @loads(
// CHECK-NOT:   "riscv.sextw"

// Instructions that compute a 32-bit result and sign-extend it: the word
// instructions and `lui`.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "word"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %0 = "riscv.addw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %1 = "riscv.addiw"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.subw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %3 = "riscv.mulw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %4 = "riscv.divw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %5 = "riscv.divuw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %6 = "riscv.remw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %7 = "riscv.remuw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %8 = "riscv.sllw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %9 = "riscv.slliw"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %10 = "riscv.srlw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %11 = "riscv.srliw"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %12 = "riscv.sraw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %13 = "riscv.sraiw"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %14 = "riscv.rolw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %15 = "riscv.rorw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %16 = "riscv.roriw"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %17 = "riscv.packw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %18 = "riscv.lui"() <{"value" = 1 : i64}> : () -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    %s4 = "riscv.sextw"(%4) : (!riscv.reg) -> !riscv.reg
    %s5 = "riscv.sextw"(%5) : (!riscv.reg) -> !riscv.reg
    %s6 = "riscv.sextw"(%6) : (!riscv.reg) -> !riscv.reg
    %s7 = "riscv.sextw"(%7) : (!riscv.reg) -> !riscv.reg
    %s8 = "riscv.sextw"(%8) : (!riscv.reg) -> !riscv.reg
    %s9 = "riscv.sextw"(%9) : (!riscv.reg) -> !riscv.reg
    %s10 = "riscv.sextw"(%10) : (!riscv.reg) -> !riscv.reg
    %s11 = "riscv.sextw"(%11) : (!riscv.reg) -> !riscv.reg
    %s12 = "riscv.sextw"(%12) : (!riscv.reg) -> !riscv.reg
    %s13 = "riscv.sextw"(%13) : (!riscv.reg) -> !riscv.reg
    %s14 = "riscv.sextw"(%14) : (!riscv.reg) -> !riscv.reg
    %s15 = "riscv.sextw"(%15) : (!riscv.reg) -> !riscv.reg
    %s16 = "riscv.sextw"(%16) : (!riscv.reg) -> !riscv.reg
    %s17 = "riscv.sextw"(%17) : (!riscv.reg) -> !riscv.reg
    %s18 = "riscv.sextw"(%18) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3, %s4, %s5, %s6, %s7, %s8, %s9, %s10, %s11, %s12, %s13, %s14, %s15, %s16, %s17, %s18) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
// CHECK-LABEL: func.func @word(
// CHECK-NOT:   "riscv.sextw"

// Counts.
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "counts"}> ({
  ^bb0(%x: !riscv.reg):
    %0 = "riscv.cpop"(%x) : (!riscv.reg) -> !riscv.reg
    %1 = "riscv.cpopw"(%x) : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.clz"(%x) : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.clzw"(%x) : (!riscv.reg) -> !riscv.reg
    %4 = "riscv.ctz"(%x) : (!riscv.reg) -> !riscv.reg
    %5 = "riscv.ctzw"(%x) : (!riscv.reg) -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    %s4 = "riscv.sextw"(%4) : (!riscv.reg) -> !riscv.reg
    %s5 = "riscv.sextw"(%5) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3, %s4, %s5) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
// CHECK-LABEL: func.func @counts(
// CHECK-NOT:   "riscv.sextw"

// Comparisons and bit extracts.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "bits"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %0 = "riscv.slt"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %1 = "riscv.sltu"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %2 = "riscv.slti"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.sltiu"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %4 = "riscv.bext"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %5 = "riscv.bexti"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    %s4 = "riscv.sextw"(%4) : (!riscv.reg) -> !riscv.reg
    %s5 = "riscv.sextw"(%5) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3, %s4, %s5) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
// CHECK-LABEL: func.func @bits(
// CHECK-NOT:   "riscv.sextw"

// Byte and half extensions.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "extensions"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %0 = "riscv.sextb"(%x) : (!riscv.reg) -> !riscv.reg
    %1 = "riscv.sexth"(%x) : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.zexth"(%x) : (!riscv.reg) -> !riscv.reg
    %4 = "riscv.packh"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    %s4 = "riscv.sextw"(%4) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3, %s4) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
// CHECK-LABEL: func.func @extensions(
// CHECK-NOT:   "riscv.sextw"

// Immediates, each at the boundary of its guard.
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "immediates"}> ({
  ^bb0(%x: !riscv.reg):
    %0 = "riscv.srai"(%x) <{"value" = 32 : i64}> : (!riscv.reg) -> !riscv.reg
    %1 = "riscv.srli"(%x) <{"value" = 33 : i64}> : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.andi"(%x) <{"value" = 2047 : i64}> : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.ori"(%x) <{"value" = -2048 : i64}> : (!riscv.reg) -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
// CHECK-LABEL: func.func @immediates(
// CHECK-NOT:   "riscv.sextw"

// Kept: a 64-bit load, a block argument, and each immediate just outside its
// guard.
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "kept"}> ({
  ^bb0(%x: !riscv.reg):
    %0 = "riscv.ld"(%x) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %1 = "riscv.srai"(%x) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.srli"(%x) <{"value" = 32 : i64}> : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.andi"(%x) <{"value" = -1 : i64}> : (!riscv.reg) -> !riscv.reg
    %4 = "riscv.ori"(%x) <{"value" = 2047 : i64}> : (!riscv.reg) -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    %s4 = "riscv.sextw"(%4) : (!riscv.reg) -> !riscv.reg
    %s5 = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3, %s4, %s5) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
// CHECK-LABEL:  func.func @kept(
// CHECK-COUNT-6: "riscv.sextw"
// CHECK:         "func.return"

}) : () -> ()
