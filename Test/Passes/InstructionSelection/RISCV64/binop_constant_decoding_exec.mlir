// RUN: veir-interpret %s | filecheck %s --check-prefix=RESULT
// RUN: veir-opt %s --print-op-generic -p=isel-sdag-riscv64 > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=RESULT
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// Immediate arithmetic, masks, and shifts use the typed constant value.
// Cover extension from the attribute width and truncation to the result width.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i32)}> ({
    %x = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
    %minusOne = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %sum = "llvm.add"(%x, %minusOne) : (i64, i64) -> i64
    %masked = "llvm.and"(%x, %minusOne) : (i64, i64) -> i64
    %shifted = "llvm.shl"(%x, %one) : (i64, i64) -> i64
    %one32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %truncatedOne = "llvm.mlir.constant"() <{value = 4294967297 : i64}> : () -> i32
    %sum32 = "llvm.add"(%one32, %truncatedOne) : (i32, i32) -> i32
    "func.return"(%sum, %masked, %shifted, %sum32) : (i64, i64, i64, i32) -> ()
  }) : () -> ()
}) : () -> ()

// RESULT: Program output: #[0x00000000000000ff#64, 0x0000000000000100#64, 0x0000000000000200#64, 0x00000002#32]
// ISEL: "riscv.addi"({{.*}}) <{"value" = -1 : i64}>
// ISEL: "riscv.andi"({{.*}}) <{"value" = -1 : i64}>
// ISEL: "riscv.slli"({{.*}}) <{"value" = 1 : i64}>
// ISEL: "riscv.addiw"({{.*}}) <{"value" = 1 : i64}>
