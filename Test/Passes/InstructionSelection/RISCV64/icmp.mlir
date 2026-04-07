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
 
    ^bb2(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.slt"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1
        
    ^bb3(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 3 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.slt"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // note: operands are swapped – rhs before lhs
        // CHECK-NEXT: %{{.*}} = "riscv.xori"(%{{.*}}) <{"immediate" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1
        
    ^bb4(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.slt"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1
        
    ^bb5(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 5 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.slt"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.xori"(%{{.*}}) <{"immediate" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1
        
    ^bb6(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.sltu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1
        
    ^bb7(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 7 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.sltu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // note: operands are swapped – rhs before lhs
        // CHECK-NEXT: %{{.*}} = "riscv.xori"(%{{.*}}) <{"immediate" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1
        
    ^bb8(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 8 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.sltu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1
        
    ^bb9(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 9 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.sltu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.xori"(%{{.*}}) <{"immediate" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i1
    }) : () -> ()
}) : () -> ()
   