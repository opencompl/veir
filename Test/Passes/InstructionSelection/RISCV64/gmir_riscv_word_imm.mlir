// RUN: veir-opt %s -p=riscv | filecheck %s

// Checks the lowering of the `gmir_riscv` word operations with a constant operand to the
// immediate instructions.

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %x = "test.test"() : () -> i64
        %c1 = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
        %c_neg2048 = "gmir.g_constant"() <{value = -2048 : i64}> : () -> i64
        %c2047 = "gmir.g_constant"() <{value = 2047 : i64}> : () -> i64
        %c2048 = "gmir.g_constant"() <{value = 2048 : i64}> : () -> i64
        %c31 = "gmir.g_constant"() <{value = 31 : i64}> : () -> i64
        %c32 = "gmir.g_constant"() <{value = 32 : i64}> : () -> i64
        // CHECK:      "riscv.addiw"(%{{.*}}) <{"value" = -2048 : i64}>
        %addw_min = "gmir_riscv.g_addw"(%x, %c_neg2048) : (i64, i64) -> i64
        // CHECK:      "riscv.addiw"(%{{.*}}) <{"value" = 2047 : i64}>
        %addw_max = "gmir_riscv.g_addw"(%x, %c2047) : (i64, i64) -> i64
        // CHECK:      "riscv.slliw"(%{{.*}}) <{"value" = 31 : i64}>
        %sllw = "gmir_riscv.g_sllw"(%x, %c31) : (i64, i64) -> i64
        // CHECK:      "riscv.srliw"(%{{.*}}) <{"value" = 1 : i64}>
        %srlw = "gmir_riscv.g_srlw"(%x, %c1) : (i64, i64) -> i64
        // CHECK:      "riscv.sraiw"(%{{.*}}) <{"value" = 1 : i64}>
        %sraw = "gmir_riscv.g_sraw"(%x, %c1) : (i64, i64) -> i64
        // A constant that does not fit the immediate is kept in a register.
        // CHECK:      "riscv.addw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        %addw_2048 = "gmir_riscv.g_addw"(%x, %c2048) : (i64, i64) -> i64
        // CHECK:      "riscv.sllw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        %sllw_32 = "gmir_riscv.g_sllw"(%x, %c32) : (i64, i64) -> i64
        "test.test"(%addw_min, %addw_max, %sllw, %srlw, %sraw, %addw_2048, %sllw_32)
            : (i64, i64, i64, i64, i64, i64, i64) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
