// Compute the 10th prime in pre-regalloc RISC-V, translated from clang output
// (clang --target=riscv64 -march=rva23u64 -O0).
//
// Register -> SSA-value mapping (physical registers that are live across
// block boundaries in the assembly become block arguments here):
//   a0 = last_prime / return value
//   a1 = count
//   a2 = n
//   a3 = trial divisor i
//   a4 = scratch
//   a5 = prime flag (always 1 on the path that reaches BB0_1)
//   a6 = constant 4
//   a7 = constant 10
//
// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    // %bb.0: entry
    ^entry():
      %a0_0 = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg   // li a0, 0
      %a1_0 = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg   // li a1, 0
      %a2_0 = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg   // li a2, 2
      %a6   = "riscv.li"() <{"value" = 4 : i64}> : () -> !riscv.reg   // li a6, 4
      %a7   = "riscv.li"() <{"value" = 10 : i64}> : () -> !riscv.reg  // li a7, 10
      // j .LBB0_2   (forward {a0,a1,a2,a6,a7})
      "riscv_cf.branch"(%a0_0, %a1_0, %a2_0, %a6, %a7) [^bb2]
        : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // .LBB0_2: for.cond.preheader   args {a0,a1,a2,a6,a7}
    ^bb2(%b2_a0 : !riscv.reg, %b2_a1 : !riscv.reg, %b2_a2 : !riscv.reg, %b2_a6 : !riscv.reg, %b2_a7 : !riscv.reg):
      %a5 = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg     // li a5, 1
      // bltu a2, a6, .LBB0_1   (taken -> ^bb1 {a1,a2,a5,a6,a7}; fall -> ^bb3 {a0,a1,a2,a5,a6,a7})
      "riscv_cf.bltu"(%b2_a2, %b2_a6,
                      %b2_a1, %b2_a2, %a5, %b2_a6, %b2_a7,
                      %b2_a0, %b2_a1, %b2_a2, %a5, %b2_a6, %b2_a7) [^bb1, ^bb3]
        <{"operandSegmentSizes" = array<i64: 1, 1, 5, 6>}>
        : (!riscv.reg, !riscv.reg,
           !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg,
           !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // .LBB0_1:   args {a1,a2,a5,a6,a7}
    ^bb1(%b1_a1 : !riscv.reg, %b1_a2 : !riscv.reg, %b1_a5 : !riscv.reg, %b1_a6 : !riscv.reg, %b1_a7 : !riscv.reg):
      %b1_a0 = "riscv.mv"(%b1_a2) : (!riscv.reg) -> !riscv.reg              // mv   a0, a2
      %b1_a1n = "riscv.addw"(%b1_a1, %b1_a5) : (!riscv.reg, !riscv.reg) -> !riscv.reg  // addw a1, a1, a5
      %b1_a2n = "riscv.addiw"(%b1_a2) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg // addiw a2, a2, 1
      // bgeu a1, a7, .LBB0_7   (taken -> ^bb7 {a0}; fall -> ^bb2 {a0,a1,a2,a6,a7})
      "riscv_cf.bgeu"(%b1_a1n, %b1_a7,
                      %b1_a0,
                      %b1_a0, %b1_a1n, %b1_a2n, %b1_a6, %b1_a7) [^bb7, ^bb2]
        <{"operandSegmentSizes" = array<i64: 1, 1, 1, 5>}>
        : (!riscv.reg, !riscv.reg,
           !riscv.reg,
           !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // %bb.3: for.body.preheader   args {a0,a1,a2,a5,a6,a7}
    ^bb3(%b3_a0 : !riscv.reg, %b3_a1 : !riscv.reg, %b3_a2 : !riscv.reg, %b3_a5 : !riscv.reg, %b3_a6 : !riscv.reg, %b3_a7 : !riscv.reg):
      %a3 = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg     // li a3, 3
      // (fall through into .LBB0_4)   forward {a0,a1,a2,a3,a5,a6,a7}
      "riscv_cf.branch"(%b3_a0, %b3_a1, %b3_a2, %a3, %b3_a5, %b3_a6, %b3_a7) [^bb4]
        : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // .LBB0_4: for.body   args {a0,a1,a2,a3,a5,a6,a7}
    ^bb4(%b4_a0 : !riscv.reg, %b4_a1 : !riscv.reg, %b4_a2 : !riscv.reg, %b4_a3 : !riscv.reg, %b4_a5 : !riscv.reg, %b4_a6 : !riscv.reg, %b4_a7 : !riscv.reg):
      %b4_a4_0 = "riscv.addi"(%b4_a3) <{"value" = -1 : i12}> : (!riscv.reg) -> !riscv.reg     // addi  a4, a3, -1
      %b4_a4 = "riscv.remuw"(%b4_a2, %b4_a4_0) : (!riscv.reg, !riscv.reg) -> !riscv.reg       // remuw a4, a2, a4
      %b4_zero = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg                        // (x0 for beqz)
      // beqz a4, .LBB0_6  ==  beq a4, x0, .LBB0_6
      //   (taken -> ^bb6 {a0,a1,a2,a6,a7}; fall -> ^bb5 {a0,a1,a2,a3,a5,a6,a7})
      "riscv_cf.beq"(%b4_a4, %b4_zero,
                     %b4_a0, %b4_a1, %b4_a2, %b4_a6, %b4_a7,
                     %b4_a0, %b4_a1, %b4_a2, %b4_a3, %b4_a5, %b4_a6, %b4_a7) [^bb6, ^bb5]
        <{"operandSegmentSizes" = array<i64: 1, 1, 5, 7>}>
        : (!riscv.reg, !riscv.reg,
           !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg,
           !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // %bb.5: for.cond   args {a0,a1,a2,a3,a5,a6,a7}
    ^bb5(%b5_a0 : !riscv.reg, %b5_a1 : !riscv.reg, %b5_a2 : !riscv.reg, %b5_a3 : !riscv.reg, %b5_a5 : !riscv.reg, %b5_a6 : !riscv.reg, %b5_a7 : !riscv.reg):
      %b5_a4 = "riscv.mulw"(%b5_a3, %b5_a3) : (!riscv.reg, !riscv.reg) -> !riscv.reg           // mulw a4, a3, a3
      %b5_a3n = "riscv.addi"(%b5_a3) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg         // addi a3, a3, 1
      // bgeu a2, a4, .LBB0_4   (taken -> ^bb4 {a0,a1,a2,a3,a5,a6,a7} with a3=a3n;
      //                         fall  -> j .LBB0_1 -> ^bb1 {a1,a2,a5,a6,a7})
      "riscv_cf.bgeu"(%b5_a2, %b5_a4,
                      %b5_a0, %b5_a1, %b5_a2, %b5_a3n, %b5_a5, %b5_a6, %b5_a7,
                      %b5_a1, %b5_a2, %b5_a5, %b5_a6, %b5_a7) [^bb4, ^bb1]
        <{"operandSegmentSizes" = array<i64: 1, 1, 7, 5>}>
        : (!riscv.reg, !riscv.reg,
           !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg,
           !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // .LBB0_6:   args {a0,a1,a2,a6,a7}
    ^bb6(%b6_a0 : !riscv.reg, %b6_a1 : !riscv.reg, %b6_a2 : !riscv.reg, %b6_a6 : !riscv.reg, %b6_a7 : !riscv.reg):
      %b6_a1s = "riscv.sextw"(%b6_a1) : (!riscv.reg) -> !riscv.reg                 // sext.w a1, a1
      %b6_a2n = "riscv.addiw"(%b6_a2) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg  // addiw a2, a2, 1
      // bltu a1, a7, .LBB0_2   (taken -> ^bb2 {a0,a1,a2,a6,a7} with a1=a1s,a2=a2n;
      //                         fall  -> ^bb7 {a0})
      "riscv_cf.bltu"(%b6_a1s, %b6_a7,
                      %b6_a0, %b6_a1s, %b6_a2n, %b6_a6, %b6_a7,
                      %b6_a0) [^bb2, ^bb7]
        <{"operandSegmentSizes" = array<i64: 1, 1, 5, 1>}>
        : (!riscv.reg, !riscv.reg,
           !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg,
           !riscv.reg) -> ()

    // .LBB0_7: while.end   args {a0}
    ^bb7(%b7_a0 : !riscv.reg):
      "func.return"(%b7_a0) : (!riscv.reg) -> ()    // ret (return value in a0)
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000001d#64]
