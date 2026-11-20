// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Only legal gMIR is selected: narrower widths must be widened by `legalize-riscv64` first.

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %constant = "gmir.g_constant"() <{value = -1 : i32}> : () -> i32
        // CHECK: %{{.*}} = "gmir.g_constant"() <{"value" = -1 : i32}> : () -> i32
        "test.test"(%constant) : (i32) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
