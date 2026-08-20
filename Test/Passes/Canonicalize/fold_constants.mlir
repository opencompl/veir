// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// The canonicalizer evaluates fully constant operations through the interpreter
// and uses each source dialect's materialization hook for the result.
"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "arith_chain"}> ({
    %c2 = "arith.constant"() <{"value" = 2 : i32}> : () -> i32
    %c3 = "arith.constant"() <{"value" = 3 : i32}> : () -> i32
    %c4 = "arith.constant"() <{"value" = 4 : i32}> : () -> i32
    %sum = "arith.addi"(%c2, %c3) : (i32, i32) -> i32
    %product = "arith.muli"(%sum, %c4) : (i32, i32) -> i32
    // CHECK-LABEL: "sym_name" = "arith_chain"
    // CHECK: %[[C20:.*]] = "arith.constant"() <{"value" = 20 : i32}> : () -> i32
    // CHECK-NEXT: "func.return"(%[[C20]]) : (i32) -> ()
    "func.return"(%product) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{function_type = () -> i64, sym_name = "llvm_add"}> ({
    %c7 = "llvm.mlir.constant"() <{"value" = 7 : i64}> : () -> i64
    %c8 = "llvm.mlir.constant"() <{"value" = 8 : i64}> : () -> i64
    %sum = "llvm.add"(%c7, %c8) : (i64, i64) -> i64
    // CHECK-LABEL: "sym_name" = "llvm_add"
    // CHECK: %[[C15:.*]] = "llvm.mlir.constant"() <{"value" = 15 : i64}> : () -> i64
    // CHECK-NEXT: "func.return"(%[[C15]]) : (i64) -> ()
    "func.return"(%sum) : (i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "riscv_addi"}> ({
    %c41 = "riscv.li"() <{"value" = 41 : i64}> : () -> !riscv.reg
    %answer = "riscv.addi"(%c41) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg
    // CHECK-LABEL: "sym_name" = "riscv_addi"
    // CHECK: %[[C42:.*]] = "riscv.li"() <{"value" = 42 : i64}> : () -> !riscv.reg
    // CHECK-NEXT: "func.return"(%[[C42]]) : (!riscv.reg) -> ()
    "func.return"(%answer) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = () -> i32, sym_name = "constant_ub"}> ({
    %c5 = "arith.constant"() <{"value" = 5 : i32}> : () -> i32
    %c0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %result = "arith.divsi"(%c5, %c0) : (i32, i32) -> i32
    // CHECK-LABEL: "sym_name" = "constant_ub"
    // CHECK: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> i32
    // CHECK-NEXT: "func.return"(%[[POISON]]) : (i32) -> ()
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()

  // Every result of a multi-result operation folds. 254 * 3 = 762 = 0x02fa, so
  // the low word is 0xfa, which prints as the signed `i8` -6, and the high
  // word is 0x02.
  "func.func"() <{function_type = () -> (i8, i8), sym_name = "extended_multiply"}> ({
    %c254 = "arith.constant"() <{"value" = 254 : i8}> : () -> i8
    %c3 = "arith.constant"() <{"value" = 3 : i8}> : () -> i8
    %lo, %hi = "arith.mului_extended"(%c254, %c3) : (i8, i8) -> (i8, i8)
    // CHECK-LABEL: "sym_name" = "extended_multiply"
    // CHECK: %[[LO:.*]] = "arith.constant"() <{"value" = -6 : i8}> : () -> i8
    // CHECK-NEXT: %[[HI:.*]] = "arith.constant"() <{"value" = 2 : i8}> : () -> i8
    // CHECK-NEXT: "func.return"(%[[LO]], %[[HI]]) : (i8, i8) -> ()
    "func.return"(%lo, %hi) : (i8, i8) -> ()
  }) : () -> ()

  // The two results of an extended add have different types, and only the `i1`
  // overflow flag is used here. The constant materialized for the unused sum is
  // trivially dead, so the greedy driver erases it again.
  "func.func"() <{function_type = () -> i1, sym_name = "extended_add_flag"}> ({
    %c255 = "arith.constant"() <{"value" = 255 : i8}> : () -> i8
    %c1 = "arith.constant"() <{"value" = 1 : i8}> : () -> i8
    %sum, %overflow = "arith.addui_extended"(%c255, %c1) : (i8, i8) -> (i8, i1)
    // CHECK-LABEL: "sym_name" = "extended_add_flag"
    // CHECK: %[[FLAG:.*]] = "arith.constant"() <{"value" = -1 : i1}> : () -> i1
    // CHECK-NEXT: "func.return"(%[[FLAG]]) : (i1) -> ()
    "func.return"(%overflow) : (i1) -> ()
  }) : () -> ()

  // An `nsw` addition that overflows is UB, so it folds to poison too. Arith
  // has no poison operation of its own and reaches for LLVM's.
  "func.func"() <{function_type = () -> i32, sym_name = "nsw_overflow"}> ({
    %cmax = "arith.constant"() <{"value" = 2147483647 : i32}> : () -> i32
    %c1 = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
    %sum = "arith.addi"(%cmax, %c1) <{overflowFlags = #arith.overflow<nsw>}> : (i32, i32) -> i32
    // CHECK-LABEL: "sym_name" = "nsw_overflow"
    // CHECK: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> i32
    // CHECK-NEXT: "func.return"(%[[POISON]]) : (i32) -> ()
    "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // LLVM spells poison itself, so a division by zero in that dialect reaches
  // the same operation by a different route.
  "func.func"() <{function_type = () -> i32, sym_name = "llvm_sdiv_zero"}> ({
    %c5 = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
    %c0 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
    %quotient = "llvm.sdiv"(%c5, %c0) : (i32, i32) -> i32
    // CHECK-LABEL: "sym_name" = "llvm_sdiv_zero"
    // CHECK: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> i32
    // CHECK-NEXT: "func.return"(%[[POISON]]) : (i32) -> ()
    "func.return"(%quotient) : (i32) -> ()
  }) : () -> ()

  // A `riscv.li` immediate is signed, so a negative register value survives
  // the round trip through materialization.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "riscv_negative"}> ({
    %cneg = "riscv.li"() <{"value" = -78 : i64}> : () -> !riscv.reg
    %sum = "riscv.addi"(%cneg) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg
    // CHECK-LABEL: "sym_name" = "riscv_negative"
    // CHECK: %[[CNEG:.*]] = "riscv.li"() <{"value" = -77 : i64}> : () -> !riscv.reg
    // CHECK-NEXT: "func.return"(%[[CNEG]]) : (!riscv.reg) -> ()
    "func.return"(%sum) : (!riscv.reg) -> ()
  }) : () -> ()

  // `comb` has no constant of its own and materializes an `hw.constant`.
  "func.func"() <{function_type = () -> i32, sym_name = "comb_add"}> ({
    %c3 = "hw.constant"() <{"value" = 3 : i32}> : () -> i32
    %c4 = "hw.constant"() <{"value" = 4 : i32}> : () -> i32
    %sum = "comb.add"(%c3, %c4) : (i32, i32) -> i32
    // CHECK-LABEL: "sym_name" = "comb_add"
    // CHECK: %[[C7:.*]] = "hw.constant"() <{"value" = 7 : i32}> : () -> i32
    // CHECK-NEXT: "func.return"(%[[C7]]) : (i32) -> ()
    "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // A `mod_arith` result is materialized as a `mod_arith.constant`, already
  // reduced modulo the type's modulus: 200 + 50 = 250 in [0, 251).
  "func.func"() <{function_type = () -> !mod_arith.int<251 : i8>, sym_name = "mod_arith_add"}> ({
    %c200 = "mod_arith.constant"() <{"value" = 200 : i8}> : () -> !mod_arith.int<251 : i8>
    %c50 = "mod_arith.constant"() <{"value" = 50 : i8}> : () -> !mod_arith.int<251 : i8>
    %sum = "mod_arith.add"(%c200, %c50)
      : (!mod_arith.int<251 : i8>, !mod_arith.int<251 : i8>) -> !mod_arith.int<251 : i8>
    // CHECK-LABEL: "sym_name" = "mod_arith_add"
    // CHECK: %[[C250:.*]] = "mod_arith.constant"() <{"value" = 250 : i8}> : () -> !mod_arith.int<251 : i8>
    // CHECK-NEXT: "func.return"(%[[C250]]) : (!mod_arith.int<251 : i8>) -> ()
    "func.return"(%sum) : (!mod_arith.int<251 : i8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "arith.addi"
// CHECK-NOT: "arith.muli"
// CHECK-NOT: "llvm.add"
// CHECK-NOT: "riscv.addi"
// CHECK-NOT: "arith.divsi"
// CHECK-NOT: "arith.mului_extended"
// CHECK-NOT: "arith.addui_extended"
// CHECK-NOT: "llvm.sdiv"
// CHECK-NOT: "comb.add"
// CHECK-NOT: "mod_arith.add"
