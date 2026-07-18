// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

// Zba: `shl (zext i32->i64 x) (const in [0,31])` selects to slli.uw
// (LLVM: `(i64 (shl (and GPR, 0xFFFFFFFF), uimm5)) -> SLLI_UW`; our `zext` is the
// 32-bit zero-extend that LLVM expresses as `and ..., 0xffffffff`).

"builtin.module"() ({
    // shl (zext x) 3 -> riscv.slliuw x 3
    "func.func"() <{function_type = (i32) -> i64, sym_name = "foo"}> ({
    ^bb(%a: i32):
        %z = "llvm.zext"(%a) : (i32) -> i64
        %c = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
        %r = "llvm.shl"(%z, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slliuw"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
