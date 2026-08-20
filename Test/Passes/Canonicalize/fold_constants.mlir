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
}) : () -> ()

// CHECK-NOT: "arith.addi"
// CHECK-NOT: "arith.muli"
// CHECK-NOT: "llvm.add"
// CHECK-NOT: "riscv.addi"
// CHECK-NOT: "arith.divsi"
// CHECK-NOT: "arith.mului_extended"
// CHECK-NOT: "arith.addui_extended"
