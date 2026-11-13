// RUN: veir-opt %s --print-op-generic -p=riscv | veir-interpret | filecheck %s

// i1 exposes incorrect sign extension; i64 extremes expose overflow from
// subtracting the operands instead of comparing them. Exercise both orders and
// negative results at different widths without requiring a particular lowering.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i2, i2, i2, i64, i64, i32)}> ({
    %one1 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %zero1 = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    %min64 = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %max64 = "llvm.mlir.constant"() <{value = 9223372036854775807 : i64}> : () -> i64

    %s1 = "llvm.intr.scmp"(%one1, %zero1) : (i1, i1) -> i2
    %u1 = "llvm.intr.ucmp"(%one1, %zero1) : (i1, i1) -> i2
    %s64 = "llvm.intr.scmp"(%min64, %max64) : (i64, i64) -> i2
    %u64 = "llvm.intr.ucmp"(%min64, %max64) : (i64, i64) -> i64
    %s64rev = "llvm.intr.scmp"(%max64, %min64) : (i64, i64) -> i64
    %u64rev = "llvm.intr.ucmp"(%max64, %min64) : (i64, i64) -> i32
    "func.return"(%s1, %u1, %s64, %u64, %s64rev, %u64rev) : (i2, i2, i2, i64, i64, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x3#2, 0x1#2, 0x3#2, 0x0000000000000001#64, 0x0000000000000001#64, 0xffffffff#32]
