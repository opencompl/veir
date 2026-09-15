// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s --check-prefixes=ISEL,WORD
// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s --check-prefix=WORD

// The i1 attribute -1 zero-extends to a rotate count of +1.
// Left rotates use right-rotate immediates of 63 (i64) or 31 (i32).
"builtin.module"() ({
  "func.func"() <{sym_name = "rotate_constants", function_type = (i64, i32) -> (i64, i64, i32, i32)}> ({
  ^bb0(%x: i64, %y: i32):
    %amount64 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %right64 = "llvm.intr.fshr"(%x, %x, %amount64) : (i64, i64, i64) -> i64
    %left64 = "llvm.intr.fshl"(%x, %x, %amount64) : (i64, i64, i64) -> i64
    %amount32 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i32
    %right32 = "llvm.intr.fshr"(%y, %y, %amount32) : (i32, i32, i32) -> i32
    %left32 = "llvm.intr.fshl"(%y, %y, %amount32) : (i32, i32, i32) -> i32
    "func.return"(%right64, %left64, %right32, %left32) : (i64, i64, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// ISEL: "riscv.rori"({{.*}}) <{"value" = 1 : i64}>
// ISEL: "riscv.rori"({{.*}}) <{"value" = 63 : i64}>
// WORD: "riscv.roriw"({{.*}}) <{"value" = 1 : i64}>
// WORD: "riscv.roriw"({{.*}}) <{"value" = 31 : i64}>
