// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %frame_index = "gmir.g_frame_index"() <{size = 24 : i64, alignment = 16 : i64}> : () -> !llvm.ptr
        // CHECK:      %[[ALLOCA:.*]] = "riscv_stack.alloca"() <{"alignment" = 16 : i64, "size" = 24 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[ALLOCA]]) : (!riscv.reg) -> !llvm.ptr
        "test.test"(%frame_index) : (!llvm.ptr) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
