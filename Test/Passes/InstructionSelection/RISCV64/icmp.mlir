// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{predicate = 0 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.xor"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sltiu"(%{{.*}}) <{"immediate" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1

    ^bb1(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{predicate = 1 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.xor"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sltiu"(%{{.*}}) <{"immediate" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1

    }) : () -> ()
}) : () -> ()
   