// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Pointer comparisons lower exactly like `i64` comparisons: a pointer fills a
// whole register, so no sign-extension prologue is needed.

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr, !llvm.ptr) -> (), sym_name = "foo"}> ({
    ^bb0(%a: !llvm.ptr, %b: !llvm.ptr):
        %r_0 = "llvm.icmp"(%a, %b) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
        // CHECK:      [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.xor"([[B]], [[A]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.sltiu"([[C]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!riscv.reg) -> i1
        %r_1 = "llvm.icmp"(%a, %b) <{predicate = 1 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.xor"([[B]], [[A]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: [[E:%.*]] = "riscv.sltu"([[D]], [[C]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[F:%.*]] = "builtin.unrealized_conversion_cast"([[E]]) : (!riscv.reg) -> i1
        %r_2 = "llvm.icmp"(%a, %b) <{predicate = 2 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.slt"([[A]], [[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!riscv.reg) -> i1
        %r_6 = "llvm.icmp"(%a, %b) <{predicate = 6 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[A]], [[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[D:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (!riscv.reg) -> i1
        %r_9 = "llvm.icmp"(%a, %b) <{predicate = 9 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
        // CHECK-NEXT: [[A:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[B:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: [[C:%.*]] = "riscv.sltu"([[A]], [[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[D:%.*]] = "riscv.xori"([[C]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: [[E:%.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (!riscv.reg) -> i1
        "test.test"(%r_0, %r_1, %r_2, %r_6, %r_9) : (i1, i1, i1, i1, i1) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
