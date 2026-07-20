// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

// Immediate-form comparison selection: when the rhs is a constant fitting a
// signed 12-bit immediate, `icmp` lowers directly to `slti`/`sltiu` (with an
// `xori _ 1` inversion for `>=`, and the `x <= C == x < C+1` off-by-one for
// `<=`). Verified sound by `icmp_refinement_*_imm` in Proofs.lean. The `>`
// predicates (sgt/ugt) are intentionally left to the reg-reg lowering (same
// cost, and better for `> 0` via x0), so they are not exercised here.

"builtin.module"() ({
    // sge: a >=s 5  ->  xori (slti a 5) 1
    "func.func"() <{function_type = (i64) -> (i1), sym_name = "f0"}> ({
    ^bb0(%a: i64):
        %z = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %z) <{predicate = 5 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: "func.func"
        // CHECK: "riscv.slti"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK: "riscv.xori"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NOT: "llvm.icmp"
    }) : () -> ()

    // uge: a >=u 5  ->  xori (sltiu a 5) 1
    "func.func"() <{function_type = (i64) -> (i1), sym_name = "f1"}> ({
    ^bb0(%a: i64):
        %z = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %z) <{predicate = 9 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: "func.func"
        // CHECK: "riscv.sltiu"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK: "riscv.xori"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NOT: "llvm.icmp"
    }) : () -> ()

    // sle: a <=s 5  ->  slti a 6   (x <= C  ==  x < C+1)
    "func.func"() <{function_type = (i64) -> (i1), sym_name = "f2"}> ({
    ^bb0(%a: i64):
        %z = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %z) <{predicate = 3 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: "func.func"
        // CHECK: "riscv.slti"(%{{.*}}) <{"value" = 6 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.xori"
        // CHECK-NOT: "llvm.icmp"
    }) : () -> ()

    // ule: a <=u 5  ->  sltiu a 6
    "func.func"() <{function_type = (i64) -> (i1), sym_name = "f3"}> ({
    ^bb0(%a: i64):
        %z = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %z) <{predicate = 7 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: "func.func"
        // CHECK: "riscv.sltiu"(%{{.*}}) <{"value" = 6 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.xori"
        // CHECK-NOT: "llvm.icmp"
    }) : () -> ()

    // Bail: sle against 2047 would need immediate 2048, which does not fit a
    // signed 12-bit field, so the peephole defers to the reg-reg lowering and
    // the `llvm.icmp` is left for `isel-riscv64` (not run here).
    "func.func"() <{function_type = (i64) -> (i1), sym_name = "f4"}> ({
    ^bb0(%a: i64):
        %z = "llvm.mlir.constant"() <{value = 2047 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %z) <{predicate = 3 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: "func.func"
        // CHECK: "llvm.icmp"
        // CHECK-NOT: "riscv.slti"
    }) : () -> ()

    // Bail: ule against -1 (unsigned UINT_MAX) is excluded, since C+1 wraps to 0.
    "func.func"() <{function_type = (i64) -> (i1), sym_name = "f5"}> ({
    ^bb0(%a: i64):
        %z = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %z) <{predicate = 7 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: "func.func"
        // CHECK: "llvm.icmp"
        // CHECK-NOT: "riscv.sltiu"
    }) : () -> ()
}) : () -> ()
