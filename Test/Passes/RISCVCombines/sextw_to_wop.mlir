// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %lhs = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
    %rhs = "riscv.li"() <{value = 2 : i64}> : () -> !riscv.reg
    // CHECK:      %[[LHS:.*]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
    // CHECK-NEXT: %[[RHS:.*]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
    %add = "riscv.add"(%lhs, %rhs) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sadd = "riscv.sextw"(%add) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "riscv.addw"(%[[LHS]], %[[RHS]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sub = "riscv.sub"(%lhs, %rhs) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %ssub = "riscv.sextw"(%sub) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "riscv.subw"(%[[LHS]], %[[RHS]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // `add` has another user, so it stays.
    %add2 = "riscv.add"(%lhs, %rhs) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sadd2 = "riscv.sextw"(%add2) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "riscv.add"(%[[LHS]], %[[RHS]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "riscv.addw"(%[[LHS]], %[[RHS]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "test.test"(%sadd, %ssub, %add2, %sadd2) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
