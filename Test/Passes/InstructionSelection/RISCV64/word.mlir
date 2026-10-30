// RUN: veir-opt %s -p=riscv | filecheck %s

// Word (`*w`) immediate selection. Legalization widens i32 arithmetic to the gMIR
// word operations (`g_addw`, `g_shlw`, ...), and isel selects their immediate forms.
// LLVM also selects these via `binop_allwusers` (an i64 op all of whose users demand
// only the low 32 bits), which needs demanded-bits analysis that we do not have.

"builtin.module"() ({
    // i32 add x (const imm12) -> riscv.addiw x imm
    "func.func"() <{function_type = (i32) -> i32, sym_name = "foo"}> ({
    ^bb(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
        %r = "llvm.add"(%a, %c) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "riscv.addiw"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i32) -> ()
    }) : () -> ()

    // i32 shl x (const in [0,31]) -> riscv.slliw x imm
    "func.func"() <{function_type = (i32) -> i32, sym_name = "bar"}> ({
    ^bb(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
        %r = "llvm.shl"(%a, %c) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "riscv.slliw"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i32) -> ()
    }) : () -> ()
}) : () -> ()
