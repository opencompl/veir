// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{predicate = 0 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.xor"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.sltiu"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1

    ^bb1(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{predicate = 1 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.xor"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !reg
        // CHECK-NEXT: [[E:%.*]] = "riscv.sltu"([[D]], [[C]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[F:%.*]] = "builtin.unrealized_conversion_cast"([[E]]) : (!reg) -> i1
 
    ^bb2(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!reg) -> i1
        
    ^bb3(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 3 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[B]], [[A]]) : (!reg, !reg) -> !reg
        // note: operands are swapped – rhs before lhs
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
        
    ^bb4(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[B]], [[A]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!reg) -> i1
        
    ^bb5(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 5 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
        
    ^bb6(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!reg) -> i1
        
    ^bb7(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 7 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[B]], [[A]]) : (!reg, !reg) -> !reg
        // note: operands are swapped – rhs before lhs
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
        
    ^bb8(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 8 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[B]], [[A]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!reg) -> i1
        
    ^bb9(%a: i64, %b: i64):
        %r = "llvm.icmp"(%a, %b) <{"predicate" = 9 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
    }) : () -> ()
}) : () -> ()
