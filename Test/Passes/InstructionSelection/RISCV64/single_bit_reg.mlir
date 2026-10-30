// RUN: veir-opt %s -p=riscv | filecheck %s

// Zbs single-bit register forms: `or`/`xor`/`and` with a single bit `shl 1, x` (inverted for
// `and`) select to bset/binv/bclr, `and (lshr y x) 1` to bext, and a lone `shl 1, x` to
// `bset x0, x`.

"builtin.module"() ({
    "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bset"}> ({
    ^bb(%y: i64, %x: i64):
        %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %bit = "llvm.shl"(%one, %x) : (i64, i64) -> i64
        %r = "llvm.or"(%y, %bit) : (i64, i64) -> i64
        // CHECK:      "riscv.bset"
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "binv"}> ({
    ^bb(%y: i64, %x: i64):
        %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %bit = "llvm.shl"(%one, %x) : (i64, i64) -> i64
        %r = "llvm.xor"(%bit, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.binv"
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bclr"}> ({
    ^bb(%y: i64, %x: i64):
        %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %m1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
        %bit = "llvm.shl"(%one, %x) : (i64, i64) -> i64
        %not = "llvm.xor"(%bit, %m1) : (i64, i64) -> i64
        %r = "llvm.and"(%y, %not) : (i64, i64) -> i64
        // CHECK:      "riscv.bclr"
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bext"}> ({
    ^bb(%y: i64, %x: i64):
        %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %srl = "llvm.lshr"(%y, %x) : (i64, i64) -> i64
        %r = "llvm.and"(%srl, %one) : (i64, i64) -> i64
        // CHECK:      "riscv.bext"
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    "func.func"() <{function_type = (i64) -> i64, sym_name = "bset_zero"}> ({
    ^bb(%x: i64):
        %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %r = "llvm.shl"(%one, %x) : (i64, i64) -> i64
        // CHECK:      "riscv.bset"
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
