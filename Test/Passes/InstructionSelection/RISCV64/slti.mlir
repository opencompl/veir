// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

// icmp against a signed-12-bit constant on the right selects to slti / sltiu
// (PatGprSimm12<setlt, SLTI> / PatGprSimm12<setult, SLTIU>), and the other
// ordered predicates select to the same via an `xori _ 1` inversion and/or a
// `+1` off-by-one immediate (see icmp_imm.mlir). Out-of-range immediates fall
// through to the general icmp lowering in isel-riscv64, staying as `llvm.icmp`.

"builtin.module"() ({
    // icmp slt x (const imm12) -> riscv.slti x imm   (predicate 2 = slt)
    "func.func"() <{function_type = (i64) -> i1}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %c) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "riscv.slti"(%{{.*}}) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i1) -> ()
    }) : () -> ()

    // icmp ult x (const imm12) -> riscv.sltiu x imm   (predicate 6 = ult)
    "func.func"() <{function_type = (i64) -> i1}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 2047 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %c) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "riscv.sltiu"(%{{.*}}) <{"value" = 2047 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i1) -> ()
    }) : () -> ()

    // icmp sgt x 7 (predicate 4 = sgt) -> xori (slti x 8) 1  (x > 7 == x >= 8 == !(x < 8))
    "func.func"() <{function_type = (i64) -> i1}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %c) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "riscv.slti"(%{{.*}}) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:      %{{.*}} = "riscv.xori"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i1) -> ()
    }) : () -> ()

    // Out-of-range immediate: not selected here (stays `llvm.icmp`).
    "func.func"() <{function_type = (i64) -> i1}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 2048 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %c) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        // CHECK:      %{{.*}} = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
    }) : () -> ()
}) : () -> ()
