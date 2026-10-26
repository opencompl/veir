// RUN: veir-opt %s -p=riscv | filecheck %s

// Checks the lowering of operations with a constant operand to the immediate instructions.

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %x = "test.test"() : () -> i64
        %c5 = "gmir.g_constant"() <{value = 5 : i64}> : () -> i64
        %c_neg2048 = "gmir.g_constant"() <{value = -2048 : i64}> : () -> i64
        %c2047 = "gmir.g_constant"() <{value = 2047 : i64}> : () -> i64
        %c2048 = "gmir.g_constant"() <{value = 2048 : i64}> : () -> i64
        %c63 = "gmir.g_constant"() <{value = 63 : i64}> : () -> i64
        %c64 = "gmir.g_constant"() <{value = 64 : i64}> : () -> i64
        // CHECK:      "riscv.addi"(%{{.*}}) <{"value" = 5 : i64}>
        %add = "gmir.g_add"(%x, %c5) : (i64, i64) -> i64
        // The post-legalizer combiner turns `x - 5` into `x + -5`.
        // CHECK:      "riscv.addi"(%{{.*}}) <{"value" = -5 : i64}>
        %sub = "gmir.g_sub"(%x, %c5) : (i64, i64) -> i64
        // The post-legalizer combiner moves the constant to the rhs.
        // CHECK:      "riscv.addi"(%{{.*}}) <{"value" = 5 : i64}>
        %add_lhs = "gmir.g_add"(%c5, %x) : (i64, i64) -> i64
        // CHECK:      "riscv.andi"(%{{.*}}) <{"value" = -2048 : i64}>
        %and = "gmir.g_and"(%x, %c_neg2048) : (i64, i64) -> i64
        // CHECK:      "riscv.ori"(%{{.*}}) <{"value" = 2047 : i64}>
        %or = "gmir.g_or"(%x, %c2047) : (i64, i64) -> i64
        // CHECK:      "riscv.xori"(%{{.*}}) <{"value" = 5 : i64}>
        %xor = "gmir.g_xor"(%x, %c5) : (i64, i64) -> i64
        // CHECK:      "riscv.slli"(%{{.*}}) <{"value" = 63 : i64}>
        %shl = "gmir.g_shl"(%x, %c63) : (i64, i64) -> i64
        // CHECK:      "riscv.srli"(%{{.*}}) <{"value" = 5 : i64}>
        %lshr = "gmir.g_lshr"(%x, %c5) : (i64, i64) -> i64
        // CHECK:      "riscv.srai"(%{{.*}}) <{"value" = 5 : i64}>
        %ashr = "gmir.g_ashr"(%x, %c5) : (i64, i64) -> i64
        // A constant that does not fit the immediate is kept in a register.
        // CHECK:      "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        %add_2048 = "gmir.g_add"(%x, %c2048) : (i64, i64) -> i64
        // CHECK:      "riscv.sll"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        %shl_64 = "gmir.g_shl"(%x, %c64) : (i64, i64) -> i64
        // A constant lhs of a non-commutative operation is kept in a register.
        // CHECK:      "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        %sub_lhs = "gmir.g_sub"(%c5, %x) : (i64, i64) -> i64
        "test.test"(%add, %sub, %add_lhs, %and, %or, %xor, %shl, %lshr, %ashr, %add_2048, %shl_64, %sub_lhs) : (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
