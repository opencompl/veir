// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %constant = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
        // CHECK:      %[[LI:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[LI]]) : (!riscv.reg) -> i64
        "test.test"(%constant) : (i64) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
