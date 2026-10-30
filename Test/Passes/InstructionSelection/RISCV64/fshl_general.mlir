// RUN: veir-opt %s -p=riscv | filecheck %s

// A funnel shift with distinct data operands is a true funnel shift, not a
// rotate, so there is no single Zbb instruction for it. Legalization lowers it to
// shifts, as LLVM's `LegalizerHelper::lowerFunnelShiftAsShifts`:
//   fshl x y z -> (x << (z & (w-1))) | ((y >> 1) >> (~z & (w-1)))
//   fshr x y z -> ((x << 1) << (~z & (w-1))) | (y >> (z & (w-1)))

"builtin.module"() ({

    // General i64 fshl -> sll / (srli 1 + srl ~z) / or, no rotate instruction.
    "func.func"()  <{function_type = (i64, i64, i64) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i64, %b: i64, %s: i64):
        %r = "llvm.intr.fshl"(%a, %b, %s) : (i64, i64, i64) -> i64
        // CHECK: %[[Z:.*]] = "riscv.andi"(%{{.*}}) <{"value" = 63 : i64}>
        // CHECK: %[[NOTZ:.*]] = "riscv.xori"(%{{.*}}) <{"value" = -1 : i64}>
        // CHECK: %[[INV:.*]] = "riscv.andi"(%[[NOTZ]]) <{"value" = 63 : i64}>
        // CHECK: %[[SHX:.*]] = "riscv.sll"(%{{.*}}, %[[Z]])
        // CHECK: %[[Y1:.*]] = "riscv.srli"(%{{.*}}) <{"value" = 1 : i64}>
        // CHECK: %[[SHY:.*]] = "riscv.srl"(%[[Y1]], %[[INV]])
        // CHECK: %{{.*}} = "riscv.or"(%[[SHX]], %[[SHY]])
        // CHECK-NOT: riscv.rol
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // General i64 fshr -> (slli 1 + sll ~z) / srl / or, no rotate instruction.
    "func.func"()  <{function_type = (i64, i64, i64) -> (), sym_name = "bar"}> ({
    ^bb0(%a: i64, %b: i64, %s: i64):
        %r = "llvm.intr.fshr"(%a, %b, %s) : (i64, i64, i64) -> i64
        // CHECK: %[[Z:.*]] = "riscv.andi"(%{{.*}}) <{"value" = 63 : i64}>
        // CHECK: %[[NOTZ:.*]] = "riscv.xori"(%{{.*}}) <{"value" = -1 : i64}>
        // CHECK: %[[INV:.*]] = "riscv.andi"(%[[NOTZ]]) <{"value" = 63 : i64}>
        // CHECK: %[[X1:.*]] = "riscv.slli"(%{{.*}}) <{"value" = 1 : i64}>
        // CHECK: %[[SHX:.*]] = "riscv.sll"(%[[X1]], %[[INV]])
        // CHECK: %[[SHY:.*]] = "riscv.srl"(%{{.*}}, %[[Z]])
        // CHECK: %{{.*}} = "riscv.or"(%[[SHX]], %[[SHY]])
        // CHECK-NOT: riscv.ror
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // General i32 fshl -> the `w`-suffixed shifts (sllw / srlw / srlw / or).
    "func.func"()  <{function_type = (i32, i32, i32) -> (), sym_name = "baz"}> ({
    ^bb0(%a: i32, %b: i32, %s: i32):
        %r = "llvm.intr.fshl"(%a, %b, %s) : (i32, i32, i32) -> i32
        // CHECK: %[[Z:.*]] = "riscv.andi"(%{{.*}}) <{"value" = 31 : i64}>
        // CHECK: %[[NOTZ:.*]] = "riscv.xori"(%{{.*}}) <{"value" = -1 : i64}>
        // CHECK: %[[INV:.*]] = "riscv.andi"(%[[NOTZ]]) <{"value" = 31 : i64}>
        // CHECK: %[[SHX:.*]] = "riscv.sllw"(%{{.*}}, %[[Z]])
        // CHECK: %[[Y1:.*]] = "riscv.srlw"
        // CHECK: %[[SHY:.*]] = "riscv.srlw"(%[[Y1]], %[[INV]])
        // CHECK: %{{.*}} = "riscv.or"(%[[SHX]], %[[SHY]])
        "test.test"(%r) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
