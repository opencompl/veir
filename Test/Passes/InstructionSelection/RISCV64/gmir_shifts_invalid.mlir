// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %a = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
        %b = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
        %shl = "gmir.g_shl"(%a, %b) : (i32, i32) -> i32
        // CHECK: %{{.*}} = "gmir.g_shl"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        "test.test"(%shl) : (i32) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
