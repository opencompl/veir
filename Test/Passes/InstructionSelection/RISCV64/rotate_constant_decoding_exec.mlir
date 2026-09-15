// RUN: veir-interpret %s | filecheck %s --check-prefix=RESULT
// RUN: veir-opt %s --print-op-generic -p=isel-riscv64 > %t.isel
// RUN: veir-interpret %t.isel | filecheck %s --check-prefix=RESULT
// RUN: filecheck %s --check-prefixes=ISEL,WORD --input-file=%t.isel
// RUN: veir-opt %s --print-op-generic -p=isel-sdag-riscv64 > %t.sdag
// RUN: veir-interpret %t.sdag | filecheck %s --check-prefix=RESULT
// RUN: filecheck %s --check-prefix=WORD --input-file=%t.sdag

// At an i32/i64 result width, an i1 attribute containing -1 means +1.
// Both selectors must rotate by one, rather than by 31 or 63.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i32, i32)}> ({
    %one64 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %amount64 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %right64 = "llvm.intr.fshr"(%one64, %one64, %amount64) : (i64, i64, i64) -> i64
    %left64 = "llvm.intr.fshl"(%one64, %one64, %amount64) : (i64, i64, i64) -> i64
    %one32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %amount32 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i32
    %right32 = "llvm.intr.fshr"(%one32, %one32, %amount32) : (i32, i32, i32) -> i32
    %left32 = "llvm.intr.fshl"(%one32, %one32, %amount32) : (i32, i32, i32) -> i32
    "func.return"(%right64, %left64, %right32, %left32) : (i64, i64, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// RESULT: Program output: #[0x8000000000000000#64, 0x0000000000000002#64, 0x80000000#32, 0x00000002#32]
// ISEL: "riscv.rori"({{.*}}) <{"value" = 1 : i64}>
// ISEL: "riscv.rori"({{.*}}) <{"value" = 63 : i64}>
// WORD: "riscv.roriw"({{.*}}) <{"value" = 1 : i64}>
// WORD: "riscv.roriw"({{.*}}) <{"value" = 31 : i64}>
