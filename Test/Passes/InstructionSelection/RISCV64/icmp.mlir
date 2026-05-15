// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i64, %b: i64):
        %r_0 = "llvm.icmp"(%a, %b) <{predicate = 0 : i64}> : (i64, i64) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.xor"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.sltiu"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
        %r_1 = "llvm.icmp"(%a, %b) <{predicate = 1 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.xor"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !reg
        // CHECK-NEXT: [[E:%.*]] = "riscv.sltu"([[D]], [[C]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[F:%.*]] = "builtin.unrealized_conversion_cast"([[E]]) : (!reg) -> i1
        %r_2 = "llvm.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!reg) -> i1
        %r_3 = "llvm.icmp"(%a, %b) <{"predicate" = 3 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[B]], [[A]]) : (!reg, !reg) -> !reg
        // note: operands are swapped – rhs before lhs
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
        %r_4 = "llvm.icmp"(%a, %b) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[B]], [[A]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!reg) -> i1
        %r_5 = "llvm.icmp"(%a, %b) <{"predicate" = 5 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
        %r_6 = "llvm.icmp"(%a, %b) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!reg) -> i1
        %r_7 = "llvm.icmp"(%a, %b) <{"predicate" = 7 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[B]], [[A]]) : (!reg, !reg) -> !reg
        // note: operands are swapped – rhs before lhs
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
        %r_8 = "llvm.icmp"(%a, %b) <{"predicate" = 8 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[B]], [[A]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!reg) -> i1
        %r_9 = "llvm.icmp"(%a, %b) <{"predicate" = 9 : i64}> : (i64, i64) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[A]], [[B]]) : (!reg, !reg) -> !reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!reg) -> i1
    }) : () -> ()
}) : () -> ()
