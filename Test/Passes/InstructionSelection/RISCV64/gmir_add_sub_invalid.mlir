// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %a = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
        %b = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
        %add = "gmir.g_add"(%a, %b) : (i32, i32) -> i32
        // CHECK: %{{.*}} = "gmir.g_add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %sub = "gmir.g_sub"(%a, %b) : (i32, i32) -> i32
        // CHECK-NEXT: %{{.*}} = "gmir.g_sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        "test.test"(%add) : (i32) -> ()
        "test.test"(%sub) : (i32) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
