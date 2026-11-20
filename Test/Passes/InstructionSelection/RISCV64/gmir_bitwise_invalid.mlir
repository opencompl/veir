// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Only legal gMIR is selected: narrower widths must be widened by `legalize-riscv64` first.

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %a = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
        %b = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
        %and = "gmir.g_and"(%a, %b) : (i32, i32) -> i32
        // CHECK: %{{.*}} = "gmir.g_and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %or = "gmir.g_or"(%a, %b) : (i32, i32) -> i32
        // CHECK-NEXT: %{{.*}} = "gmir.g_or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %xor = "gmir.g_xor"(%a, %b) : (i32, i32) -> i32
        // CHECK-NEXT: %{{.*}} = "gmir.g_xor"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        "test.test"(%and) : (i32) -> ()
        "test.test"(%or) : (i32) -> ()
        "test.test"(%xor) : (i32) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
