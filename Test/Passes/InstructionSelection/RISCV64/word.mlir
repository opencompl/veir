// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

// Best-effort word (`*w`) immediate selection. LLVM triggers these via
// `binop_allwusers` (an i64 op all of whose users demand only the low 32 bits),
// which we cannot model without demanded-bits analysis; we approximate it by
// gating on an i32 result type. These therefore only fire on i32 arithmetic.

"builtin.module"() ({
    // i32 add x (const imm12) -> riscv.addiw x imm
    "func.func"() <{function_type = (i32) -> i32}> ({
    ^bb(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
        %r = "llvm.add"(%a, %c) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "riscv.addiw"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i32) -> ()
    }) : () -> ()

    // i32 shl x (const in [0,31]) -> riscv.slliw x imm
    "func.func"() <{function_type = (i32) -> i32}> ({
    ^bb(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
        %r = "llvm.shl"(%a, %c) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "riscv.slliw"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i32) -> ()
    }) : () -> ()
}) : () -> ()
