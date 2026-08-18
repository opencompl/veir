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
}) : () -> ()

// CHECK-NOT: "arith.addi"
// CHECK-NOT: "arith.muli"
// CHECK-NOT: "llvm.add"
// CHECK-NOT: "riscv.addi"
// CHECK-NOT: "arith.divsi"
