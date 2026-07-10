// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A funnel shift with distinct data operands is a true funnel shift, not a
// rotate, so there is no single Zbb instruction for it. Mirroring LLVM's generic
// `TargetLowering::expandFunnelShift`, we lower it to a shift/or expansion:
//   fshl x y z -> (x << z) | ((y >> 1) >> ~z)
//   fshr x y z -> ((x << 1) << ~z) | (y >> z)
// The RISC-V shifts mask their amount modulo the width, so `z % w` is `z` and
// `(w-1) - (z % w)` is `~z`. These fire only after the rotate/const-rotate
// matchers, so identical-operand and constant-amount cases still select rol/ror.

"builtin.module"() ({

    // General i64 fshl -> sll / (srli 1 + srl ~z) / or, no rotate instruction.
    "func.func"()  <{function_type = (i64, i64, i64) -> ()}> ({
    ^bb0(%a: i64, %b: i64, %s: i64):
        %r = "llvm.intr.fshl"(%a, %b, %s) : (i64, i64, i64) -> i64
        // CHECK: %[[NOTZ:.*]] = "riscv.xori"(%[[Z:.*]]) <{"value" = -1 : i64}>
        // CHECK: %[[SHX:.*]] = "riscv.sll"(%{{.*}}, %[[Z]])
        // CHECK: %[[Y1:.*]] = "riscv.srli"(%{{.*}}) <{"value" = 1 : i64}>
        // CHECK: %[[SHY:.*]] = "riscv.srl"(%[[Y1]], %[[NOTZ]])
        // CHECK: %{{.*}} = "riscv.or"(%[[SHX]], %[[SHY]])
        // CHECK-NOT: riscv.rol
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // General i64 fshr -> (slli 1 + sll ~z) / srl / or, no rotate instruction.
    "func.func"()  <{function_type = (i64, i64, i64) -> ()}> ({
    ^bb0(%a: i64, %b: i64, %s: i64):
        %r = "llvm.intr.fshr"(%a, %b, %s) : (i64, i64, i64) -> i64
        // CHECK: %[[NOTZ:.*]] = "riscv.xori"(%[[Z:.*]]) <{"value" = -1 : i64}>
        // CHECK: %[[X1:.*]] = "riscv.slli"(%{{.*}}) <{"value" = 1 : i64}>
        // CHECK: %[[SHX:.*]] = "riscv.sll"(%[[X1]], %[[NOTZ]])
        // CHECK: %[[SHY:.*]] = "riscv.srl"(%{{.*}}, %[[Z]])
        // CHECK: %{{.*}} = "riscv.or"(%[[SHX]], %[[SHY]])
        // CHECK-NOT: riscv.ror
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // General i32 fshl -> the `w`-suffixed shifts (sllw / srliw / srlw / or).
    "func.func"()  <{function_type = (i32, i32, i32) -> ()}> ({
    ^bb0(%a: i32, %b: i32, %s: i32):
        %r = "llvm.intr.fshl"(%a, %b, %s) : (i32, i32, i32) -> i32
        // CHECK: %[[NOTZ:.*]] = "riscv.xori"(%[[Z:.*]]) <{"value" = -1 : i64}>
        // CHECK: %[[SHX:.*]] = "riscv.sllw"(%{{.*}}, %[[Z]])
        // CHECK: %[[Y1:.*]] = "riscv.srliw"(%{{.*}}) <{"value" = 1 : i64}>
        // CHECK: %[[SHY:.*]] = "riscv.srlw"(%[[Y1]], %[[NOTZ]])
        // CHECK: %{{.*}} = "riscv.or"(%[[SHX]], %[[SHY]])
        "test.test"(%r) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
