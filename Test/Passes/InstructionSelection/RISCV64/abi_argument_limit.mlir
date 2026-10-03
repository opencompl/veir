// RUN: veir-opt %s --print-op-generic -p=isel-abi-riscv64 | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// Eight integer arguments fit in a0-a7. Calls with nine arguments must stay
// unlowered until stack arguments are supported. An indirect target pointer
// does not consume an argument register.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<i64 (i64, ptr)>}> ({
  ^bb0(%a: i64, %p: !llvm.ptr):
    %l8 = "llvm.call"(%a, %a, %a, %a, %a, %a, %a, %a) <{callee = @llvm_eight}> : (i64, i64, i64, i64, i64, i64, i64, i64) -> i64
    %l9 = "llvm.call"(%l8, %a, %a, %a, %a, %a, %a, %a, %a) <{callee = @llvm_nine}> : (i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64
    %i8 = "llvm.call"(%p, %l9, %a, %a, %a, %a, %a, %a, %a) : (!llvm.ptr, i64, i64, i64, i64, i64, i64, i64, i64) -> i64
    %i9 = "llvm.call"(%p, %i8, %a, %a, %a, %a, %a, %a, %a, %a) : (!llvm.ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64
    "llvm.return"(%i9) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "caller"
// CHECK: "riscv_cf.call"({{.*}}) <{"callee" = @llvm_eight}>
// CHECK: "llvm.call"({{.*}}) <{"callee" = @llvm_nine}> : (i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64
// CHECK: "riscv_cf.call"({{.*}}) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK: "llvm.call"({{.*}}) : (!llvm.ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64
// CHECK: "riscv_cf.return"
