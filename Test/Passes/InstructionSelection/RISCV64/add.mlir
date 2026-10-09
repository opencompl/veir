// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,isel-riscv64,reconcile-cast | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "foo"}> ({
    ^bb(%a: i64, %b: i64):
        %add = "llvm.add"(%a, %b) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %add_nsw = "llvm.add"(%a, %b) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %add_nuw = "llvm.add"(%a, %b) <{"overflowFlags" = 2 : i32}>: (i64, i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %add_nuw_nsw = "llvm.add"(%a, %b) <{"overflowFlags" = 3 : i32}>: (i64, i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        "test.test"(%add) : (i64) -> ()
        "test.test"(%add_nsw) : (i64) -> ()
        "test.test"(%add_nuw) : (i64) -> ()
        "test.test"(%add_nuw_nsw) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
