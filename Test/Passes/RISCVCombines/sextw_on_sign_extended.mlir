// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// A `sextw` is removed when its operand is already sign-extended, i.e. the
// result of a load, a word instruction, a comparison, another instruction with
// a small result, or a shift, `andi` or `ori` with a suitable immediate.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "loads"}> ({
  ^bb0(%addr: !riscv.reg):
    %w = "riscv.lw"(%addr) <{"value" = -4 : i64}> : (!riscv.reg) -> !riscv.reg
    %h = "riscv.lh"(%addr) <{"value" = 2 : i64}> : (!riscv.reg) -> !riscv.reg
    %b = "riscv.lb"(%addr) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %hu = "riscv.lhu"(%addr) <{"value" = 6 : i64}> : (!riscv.reg) -> !riscv.reg
    %bu = "riscv.lbu"(%addr) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    %sw = "riscv.sextw"(%w) : (!riscv.reg) -> !riscv.reg
    %sh = "riscv.sextw"(%h) : (!riscv.reg) -> !riscv.reg
    %sb = "riscv.sextw"(%b) : (!riscv.reg) -> !riscv.reg
    %shu = "riscv.sextw"(%hu) : (!riscv.reg) -> !riscv.reg
    %sbu = "riscv.sextw"(%bu) : (!riscv.reg) -> !riscv.reg
    "func.return"(%sw, %sh, %sb, %shu, %sbu) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "word_ops"}> ({
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
    %9 = "riscv.slliw"(%x) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %10 = "riscv.srlw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %11 = "riscv.srliw"(%x) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %12 = "riscv.sraw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %13 = "riscv.sraiw"(%x) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %14 = "riscv.rolw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %15 = "riscv.rorw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %16 = "riscv.roriw"(%x) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %17 = "riscv.clzw"(%x) : (!riscv.reg) -> !riscv.reg
    %18 = "riscv.ctzw"(%x) : (!riscv.reg) -> !riscv.reg
    %19 = "riscv.cpopw"(%x) : (!riscv.reg) -> !riscv.reg
    %20 = "riscv.packw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
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
    %s19 = "riscv.sextw"(%19) : (!riscv.reg) -> !riscv.reg
    %s20 = "riscv.sextw"(%20) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3, %s4, %s5, %s6, %s7, %s8, %s9, %s10, %s11, %s12, %s13, %s14, %s15, %s16, %s17, %s18, %s19, %s20) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "comparisons"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %0 = "riscv.slt"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %1 = "riscv.sltu"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %2 = "riscv.slti"(%x) <{"value" = -5 : i64}> : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.sltiu"(%x) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg), sym_name = "kept"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %d = "riscv.ld"(%x) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %a = "riscv.add"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sd = "riscv.sextw"(%d) : (!riscv.reg) -> !riscv.reg
    %sa = "riscv.sextw"(%a) : (!riscv.reg) -> !riscv.reg
    %sx = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    "func.return"(%sd, %sa, %sx) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "other_ops"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %0 = "riscv.clz"(%x) : (!riscv.reg) -> !riscv.reg
    %1 = "riscv.ctz"(%x) : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.cpop"(%x) : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.bext"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %4 = "riscv.bexti"(%x) <{"value" = 40 : i64}> : (!riscv.reg) -> !riscv.reg
    %5 = "riscv.sextb"(%x) : (!riscv.reg) -> !riscv.reg
    %6 = "riscv.sexth"(%x) : (!riscv.reg) -> !riscv.reg
    %7 = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %8 = "riscv.zexth"(%x) : (!riscv.reg) -> !riscv.reg
    %9 = "riscv.packh"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %10 = "riscv.lui"() <{"value" = 524288 : i64}> : () -> !riscv.reg
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
    "func.return"(%s0, %s1, %s2, %s3, %s4, %s5, %s6, %s7, %s8, %s9, %s10) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

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

  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "immediates_kept"}> ({
  ^bb0(%x: !riscv.reg):
    %0 = "riscv.srai"(%x) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
    %1 = "riscv.srli"(%x) <{"value" = 32 : i64}> : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.andi"(%x) <{"value" = -1 : i64}> : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.ori"(%x) <{"value" = 2047 : i64}> : (!riscv.reg) -> !riscv.reg
    %s0 = "riscv.sextw"(%0) : (!riscv.reg) -> !riscv.reg
    %s1 = "riscv.sextw"(%1) : (!riscv.reg) -> !riscv.reg
    %s2 = "riscv.sextw"(%2) : (!riscv.reg) -> !riscv.reg
    %s3 = "riscv.sextw"(%3) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s0, %s1, %s2, %s3) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @loads(
// CHECK-NOT: "riscv.sextw"
// CHECK: %[[W:[^ ]*]] = "riscv.lw"
// CHECK: %[[H:[^ ]*]] = "riscv.lh"
// CHECK: %[[B:[^ ]*]] = "riscv.lb"
// CHECK: %[[HU:[^ ]*]] = "riscv.lhu"
// CHECK: %[[BU:[^ ]*]] = "riscv.lbu"
// CHECK-NOT: "riscv.sextw"
// CHECK: "func.return"(%[[W]], %[[H]], %[[B]], %[[HU]], %[[BU]])

// CHECK-LABEL: func.func @word_ops(
// CHECK-NOT: "riscv.sextw"
// CHECK: %[[W0:[^ ]*]] = "riscv.addw"
// CHECK-NOT: "riscv.sextw"
// CHECK: %[[W20:[^ ]*]] = "riscv.packw"
// CHECK-NOT: "riscv.sextw"
// CHECK: "func.return"(%[[W0]], {{.*}}, %[[W20]])

// CHECK-LABEL: func.func @comparisons(
// CHECK-NOT: "riscv.sextw"
// CHECK: %[[C0:[^ ]*]] = "riscv.slt"
// CHECK-NOT: "riscv.sextw"
// CHECK: %[[C3:[^ ]*]] = "riscv.sltiu"
// CHECK-NOT: "riscv.sextw"
// CHECK: "func.return"(%[[C0]], {{.*}}, %[[C3]])

// CHECK-LABEL: func.func @kept(
// CHECK: %[[D:[^ ]*]] = "riscv.ld"
// CHECK: %[[A:[^ ]*]] = "riscv.add"
// CHECK: %[[SD:[^ ]*]] = "riscv.sextw"(%[[D]])
// CHECK: %[[SA:[^ ]*]] = "riscv.sextw"(%[[A]])
// CHECK: %[[SX:[^ ]*]] = "riscv.sextw"(%[[X:[^)]*]])
// CHECK: "func.return"(%[[SD]], %[[SA]], %[[SX]])

// CHECK-LABEL: func.func @other_ops(
// CHECK-NOT: "riscv.sextw"
// CHECK: %[[O0:[^ ]*]] = "riscv.clz"
// CHECK-NOT: "riscv.sextw"
// CHECK: %[[O10:[^ ]*]] = "riscv.lui"
// CHECK-NOT: "riscv.sextw"
// CHECK: "func.return"(%[[O0]], {{.*}}, %[[O10]])

// CHECK-LABEL: func.func @immediates(
// CHECK-NOT: "riscv.sextw"
// CHECK: %[[I0:[^ ]*]] = "riscv.srai"
// CHECK: %[[I1:[^ ]*]] = "riscv.srli"
// CHECK: %[[I2:[^ ]*]] = "riscv.andi"
// CHECK: %[[I3:[^ ]*]] = "riscv.ori"
// CHECK-NOT: "riscv.sextw"
// CHECK: "func.return"(%[[I0]], %[[I1]], %[[I2]], %[[I3]])

// CHECK-LABEL: func.func @immediates_kept(
// CHECK-COUNT-4: "riscv.sextw"
// CHECK: "func.return"
