// Compute the 10th prime in pre-regalloc RISC-V, translated from clang output
// (clang --target=riscv64 -march=rva23u64 -O0).
//
// Unregistered instructions used in this file (not in the riscv dialect):
//   riscv.lw   -- 32-bit sign-extending load word
//   riscv.sw   -- 32-bit store word
//
// RUN: VEIR_UNREGISTERED_ROUNDTRIP

// CHECK: "func.func"() <{"function_type" = (!riscv.reg, !riscv.reg, !riscv.reg) -> !riscv.reg, "sym_name" = "main"}>

"builtin.module"() ({
  // main(sp, ra, s0_caller) -- the architectural registers read on entry.
  "func.func"() <{sym_name = "main", function_type = (!riscv.reg, !riscv.reg, !riscv.reg) -> !riscv.reg}> ({
    // %bb.0: entry
    ^entry(%sp_in : !riscv.reg, %ra_in : !riscv.reg, %s0_caller : !riscv.reg):
      %fp_sp = "riscv.addi"(%sp_in) <{"value" = -48 : i12}> : (!riscv.reg) -> !riscv.reg   // addi sp, sp, -48
      "riscv.sd"(%fp_sp, %ra_in) <{"value" = 40 : i12}> : (!riscv.reg, !riscv.reg) -> ()    // sd ra, 40(sp)
      "riscv.sd"(%fp_sp, %s0_caller) <{"value" = 32 : i12}> : (!riscv.reg, !riscv.reg) -> () // sd s0, 32(sp)
      %s0 = "riscv.addi"(%fp_sp) <{"value" = 48 : i12}> : (!riscv.reg) -> !riscv.reg        // addi s0, sp, 48
      %e_a0 = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg                          // li a0, 0
      "riscv.sw"(%s0, %e_a0) <{"value" = -20 : i12}> : (!riscv.reg, !riscv.reg) -> ()        // sw a0, -20(s0)
      "riscv.sw"(%s0, %e_a0) <{"value" = -24 : i12}> : (!riscv.reg, !riscv.reg) -> ()        // sw a0, -24(s0)
      %e_a1 = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg                          // li a1, 2
      "riscv.sw"(%s0, %e_a1) <{"value" = -28 : i12}> : (!riscv.reg, !riscv.reg) -> ()        // sw a1, -28(s0)
      "riscv.sw"(%s0, %e_a0) <{"value" = -32 : i12}> : (!riscv.reg, !riscv.reg) -> ()        // sw a0, -32(s0)
      "riscv_cf.branch"(%s0) [^bb1] : (!riscv.reg) -> ()                                     // j .LBB0_1

    // .LBB0_1: while.cond
    ^bb1(%b1_s0 : !riscv.reg):
      %b1_a1 = "riscv.lw"(%b1_s0) <{"value" = -24 : i12}> : (!riscv.reg) -> !riscv.reg       // lw a1, -24(s0)
      %b1_a0 = "riscv.li"() <{"value" = 9 : i64}> : () -> !riscv.reg                          // li a0, 9
      // blt a0, a1, .LBB0_11   (taken -> ^bb11; fall -> ^bb2)
      "riscv_cf.blt"(%b1_a0, %b1_a1, %b1_s0, %b1_s0) [^bb11, ^bb2]
        <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}>
        : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // .LBB0_2: while.body
    ^bb2(%b2_s0 : !riscv.reg):
      %b2_a0 = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg                          // li a0, 1
      "riscv.sw"(%b2_s0, %b2_a0) <{"value" = -36 : i12}> : (!riscv.reg, !riscv.reg) -> ()     // sw a0, -36(s0)
      %b2_a0b = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg                         // li a0, 2
      "riscv.sw"(%b2_s0, %b2_a0b) <{"value" = -40 : i12}> : (!riscv.reg, !riscv.reg) -> ()    // sw a0, -40(s0)
      "riscv_cf.branch"(%b2_s0) [^bb3] : (!riscv.reg) -> ()                                   // j .LBB0_3

    // .LBB0_3: for.cond
    ^bb3(%b3_s0 : !riscv.reg):
      %b3_a0 = "riscv.lw"(%b3_s0) <{"value" = -40 : i12}> : (!riscv.reg) -> !riscv.reg        // lw a0, -40(s0)
      %b3_a1 = "riscv.mulw"(%b3_a0, %b3_a0) : (!riscv.reg, !riscv.reg) -> !riscv.reg          // mulw a1, a0, a0
      %b3_a0b = "riscv.lw"(%b3_s0) <{"value" = -28 : i12}> : (!riscv.reg) -> !riscv.reg       // lw a0, -28(s0)
      // blt a0, a1, .LBB0_8   (taken -> ^bb8; fall -> ^bb4)
      "riscv_cf.blt"(%b3_a0b, %b3_a1, %b3_s0, %b3_s0) [^bb8, ^bb4]
        <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}>
        : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // .LBB0_4: for.body
    ^bb4(%b4_s0 : !riscv.reg):
      %b4_a0 = "riscv.lw"(%b4_s0) <{"value" = -28 : i12}> : (!riscv.reg) -> !riscv.reg        // lw a0, -28(s0)
      %b4_a1 = "riscv.lw"(%b4_s0) <{"value" = -40 : i12}> : (!riscv.reg) -> !riscv.reg        // lw a1, -40(s0)
      %b4_a0r = "riscv.remw"(%b4_a0, %b4_a1) : (!riscv.reg, !riscv.reg) -> !riscv.reg         // remw a0, a0, a1
      %b4_zero = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg                         // (x0 for bnez)
      // bnez a0, .LBB0_6  ==  bne a0, x0   (taken -> ^bb6; fall -> ^bb5)
      "riscv_cf.bne"(%b4_a0r, %b4_zero, %b4_s0, %b4_s0) [^bb6, ^bb5]
        <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}>
        : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // .LBB0_5: if.then
    ^bb5(%b5_s0 : !riscv.reg):
      %b5_a0 = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg                          // li a0, 0
      "riscv.sw"(%b5_s0, %b5_a0) <{"value" = -36 : i12}> : (!riscv.reg, !riscv.reg) -> ()     // sw a0, -36(s0)
      "riscv_cf.branch"(%b5_s0) [^bb8] : (!riscv.reg) -> ()                                   // j .LBB0_8

    // .LBB0_6: if.end
    ^bb6(%b6_s0 : !riscv.reg):
      "riscv_cf.branch"(%b6_s0) [^bb7] : (!riscv.reg) -> ()                                   // j .LBB0_7

    // .LBB0_7: for.inc
    ^bb7(%b7_s0 : !riscv.reg):
      %b7_a0 = "riscv.lw"(%b7_s0) <{"value" = -40 : i12}> : (!riscv.reg) -> !riscv.reg        // lw a0, -40(s0)
      %b7_a0n = "riscv.addiw"(%b7_a0) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg      // addiw a0, a0, 1
      "riscv.sw"(%b7_s0, %b7_a0n) <{"value" = -40 : i12}> : (!riscv.reg, !riscv.reg) -> ()    // sw a0, -40(s0)
      "riscv_cf.branch"(%b7_s0) [^bb3] : (!riscv.reg) -> ()                                   // j .LBB0_3

    // .LBB0_8: for.end
    ^bb8(%b8_s0 : !riscv.reg):
      %b8_a0 = "riscv.lw"(%b8_s0) <{"value" = -36 : i12}> : (!riscv.reg) -> !riscv.reg        // lw a0, -36(s0)
      %b8_zero = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg                         // (x0 for beqz)
      // beqz a0, .LBB0_10  ==  beq a0, x0   (taken -> ^bb10; fall -> ^bb9)
      "riscv_cf.beq"(%b8_a0, %b8_zero, %b8_s0, %b8_s0) [^bb10, ^bb9]
        <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}>
        : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // .LBB0_9: if.then3
    ^bb9(%b9_s0 : !riscv.reg):
      %b9_a0 = "riscv.lw"(%b9_s0) <{"value" = -28 : i12}> : (!riscv.reg) -> !riscv.reg        // lw a0, -28(s0)
      "riscv.sw"(%b9_s0, %b9_a0) <{"value" = -32 : i12}> : (!riscv.reg, !riscv.reg) -> ()     // sw a0, -32(s0)
      %b9_a0b = "riscv.lw"(%b9_s0) <{"value" = -24 : i12}> : (!riscv.reg) -> !riscv.reg       // lw a0, -24(s0)
      %b9_a0n = "riscv.addiw"(%b9_a0b) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg     // addiw a0, a0, 1
      "riscv.sw"(%b9_s0, %b9_a0n) <{"value" = -24 : i12}> : (!riscv.reg, !riscv.reg) -> ()    // sw a0, -24(s0)
      "riscv_cf.branch"(%b9_s0) [^bb10] : (!riscv.reg) -> ()                                  // j .LBB0_10

    // .LBB0_10: if.end5
    ^bb10(%b10_s0 : !riscv.reg):
      %b10_a0 = "riscv.lw"(%b10_s0) <{"value" = -28 : i12}> : (!riscv.reg) -> !riscv.reg      // lw a0, -28(s0)
      %b10_a0n = "riscv.addiw"(%b10_a0) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg    // addiw a0, a0, 1
      "riscv.sw"(%b10_s0, %b10_a0n) <{"value" = -28 : i12}> : (!riscv.reg, !riscv.reg) -> ()  // sw a0, -28(s0)
      "riscv_cf.branch"(%b10_s0) [^bb1] : (!riscv.reg) -> ()                                  // j .LBB0_1

    // .LBB0_11: while.end
    ^bb11(%b11_s0 : !riscv.reg):
      %b11_a0 = "riscv.lw"(%b11_s0) <{"value" = -32 : i12}> : (!riscv.reg) -> !riscv.reg      // lw a0, -32(s0)
      %ex_sp = "riscv.addi"(%b11_s0) <{"value" = -48 : i12}> : (!riscv.reg) -> !riscv.reg     // addi sp, s0, -48
      %ex_ra = "riscv.ld"(%ex_sp) <{"value" = 40 : i12}> : (!riscv.reg) -> !riscv.reg         // ld ra, 40(sp)
      %ex_s0 = "riscv.ld"(%ex_sp) <{"value" = 32 : i12}> : (!riscv.reg) -> !riscv.reg         // ld s0, 32(sp)
      %ex_spf = "riscv.addi"(%ex_sp) <{"value" = 48 : i12}> : (!riscv.reg) -> !riscv.reg      // addi sp, sp, 48
      "func.return"(%b11_a0) : (!riscv.reg) -> ()                                             // ret (value in a0)
  }) : () -> ()
}) : () -> ()
