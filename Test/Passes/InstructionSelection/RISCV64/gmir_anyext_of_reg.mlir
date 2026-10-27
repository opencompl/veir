// RUN: veir-opt %s -p=isel-riscv64,reconcile-cast | filecheck %s

// `g_anyext` leaves its high bits unspecified, so the anyext of a value cast from a register is
// that register itself, with no zero-extension.

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void (!riscv.reg, !riscv.reg)>, sym_name = "main"}> ({
    ^bb0(%r : !riscv.reg, %s : !riscv.reg):
        %sum = "riscv.addw"(%r, %s) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        %narrow = "builtin.unrealized_conversion_cast"(%sum) : (!riscv.reg) -> i32
        %wide = "gmir.g_anyext"(%narrow) : (i32) -> i64
        %byte = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> i8
        %wide8 = "gmir.g_anyext"(%byte) : (i8) -> i64
        %x = "gmir.g_xor"(%wide, %wide8) : (i64, i64) -> i64
        // CHECK:      ^{{.*}}(%[[R:.*]] : !riscv.reg, %[[S:.*]] : !riscv.reg):
        // CHECK-NEXT: %[[SUM:.*]] = "riscv.addw"(%[[R]], %[[S]])
        // CHECK-NEXT: %{{.*}} = "riscv.xor"(%[[SUM]], %[[S]])
        // CHECK-NOT:  riscv.zext
        "test.test"(%x) : (i64) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
