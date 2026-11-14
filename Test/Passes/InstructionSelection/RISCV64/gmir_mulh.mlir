// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s
// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s --check-prefix=NARROW

// `i64` multiply-high selects; `i32` and `i13` do not, because multiply-high is
// legal at `i64` alone and no legalization widens it.

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %a = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %b = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
        %smulh = "gmir.g_smulh"(%a, %b) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.mulh"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %umulh = "gmir.g_umulh"(%a, %b) : (i64, i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.mulhu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %c = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
        %d = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
        %narrow_s = "gmir.g_smulh"(%c, %d) : (i32, i32) -> i32
        // NARROW: %{{.*}} = "gmir.g_smulh"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %narrow_u = "gmir.g_umulh"(%c, %d) : (i32, i32) -> i32
        // NARROW: %{{.*}} = "gmir.g_umulh"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %e = "llvm.mlir.constant"() <{value = 1 : i13}> : () -> i13
        %f = "llvm.mlir.constant"() <{value = 2 : i13}> : () -> i13
        %odd_s = "gmir.g_smulh"(%e, %f) : (i13, i13) -> i13
        // NARROW: %{{.*}} = "gmir.g_smulh"(%{{.*}}, %{{.*}}) : (i13, i13) -> i13
        %odd_u = "gmir.g_umulh"(%e, %f) : (i13, i13) -> i13
        // NARROW: %{{.*}} = "gmir.g_umulh"(%{{.*}}, %{{.*}}) : (i13, i13) -> i13
        "test.test"(%smulh) : (i64) -> ()
        "test.test"(%umulh) : (i64) -> ()
        "test.test"(%narrow_s) : (i32) -> ()
        "test.test"(%narrow_u) : (i32) -> ()
        "test.test"(%odd_s) : (i13) -> ()
        "test.test"(%odd_u) : (i13) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
