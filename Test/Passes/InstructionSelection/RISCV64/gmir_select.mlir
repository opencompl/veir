// RUN: veir-opt %s -p=riscv | filecheck %s

// `g_select` is selected branchlessly with Zicond, as `llvm.select`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64, i32, i32) -> (), sym_name = "main"}> ({
  ^bb0(%c: i64, %t: i64, %f: i64, %t32: i32, %f32: i32):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %select = "gmir.g_select"(%c, %t, %f) : (i64, i64, i64) -> i64
    // CHECK:      %[[T:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[F:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[EQZ:.*]] = "riscv.czeroeqz"(%[[T]], %[[C]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: %[[NEZ:.*]] = "riscv.czeronez"(%[[F]], %[[C]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: %[[OR:.*]] = "riscv.or"(%[[EQZ]], %[[NEZ]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[OR]]) : (!riscv.reg) -> i64
    %select32 = "gmir.g_select"(%c, %t32, %f32) : (i64, i32, i32) -> i32
    // CHECK:      "riscv.czeroeqz"
    // CHECK-NEXT: "riscv.czeronez"
    // CHECK-NEXT: %[[OR:.*]] = "riscv.or"
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[OR]]) : (!riscv.reg) -> i32
    // A zero value only needs one instruction.
    %select_t0 = "gmir.g_select"(%c, %t, %zero) : (i64, i64, i64) -> i64
    // CHECK:      %[[EQZ:.*]] = "riscv.czeroeqz"
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[EQZ]]) : (!riscv.reg) -> i64
    %select_0f = "gmir.g_select"(%c, %zero, %f) : (i64, i64, i64) -> i64
    // CHECK:      %[[NEZ:.*]] = "riscv.czeronez"
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[NEZ]]) : (!riscv.reg) -> i64
    "test.test"(%select, %select32, %select_t0, %select_0f) : (i64, i32, i64, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
