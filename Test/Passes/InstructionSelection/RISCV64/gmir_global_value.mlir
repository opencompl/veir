// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// An external weak global is not selected; LLVM loads its address from the GOT.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "x", value = 0 : i32}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<extern_weak>, sym_name = "y"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
    // CHECK:      %[[LA:.*]] = "riscv.la"() <{"symbol" = @x}> : () -> !riscv.reg
    // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[LA]]) : (!riscv.reg) -> !llvm.ptr
    %x = "gmir.g_global_value"() <{global_name = @x}> : () -> !llvm.ptr
    // CHECK:      "gmir.g_global_value"() <{"global_name" = @y}> : () -> !llvm.ptr
    %y = "gmir.g_global_value"() <{global_name = @y}> : () -> !llvm.ptr
    "test.test"(%x, %y) : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
