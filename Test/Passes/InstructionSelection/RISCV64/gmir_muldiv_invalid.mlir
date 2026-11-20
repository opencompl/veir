// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Only legal gMIR is selected: `i32` must be custom-legalized by `legalize-riscv64` first.

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %a = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
        %b = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
        %mul = "gmir.g_mul"(%a, %b) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "gmir.g_mul"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %sdiv = "gmir.g_sdiv"(%a, %b) : (i32, i32) -> i32
        // CHECK-NEXT: %{{.*}} = "gmir.g_sdiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %udiv = "gmir.g_udiv"(%a, %b) : (i32, i32) -> i32
        // CHECK-NEXT: %{{.*}} = "gmir.g_udiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %srem = "gmir.g_srem"(%a, %b) : (i32, i32) -> i32
        // CHECK-NEXT: %{{.*}} = "gmir.g_srem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %urem = "gmir.g_urem"(%a, %b) : (i32, i32) -> i32
        // CHECK-NEXT: %{{.*}} = "gmir.g_urem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        "test.test"(%mul) : (i32) -> ()
        "test.test"(%sdiv) : (i32) -> ()
        "test.test"(%udiv) : (i32) -> ()
        "test.test"(%srem) : (i32) -> ()
        "test.test"(%urem) : (i32) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
