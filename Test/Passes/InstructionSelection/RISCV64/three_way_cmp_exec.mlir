// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64,dce | veir-interpret | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// Signed and unsigned ordering differ at the sign bit. Exercise that boundary
// for i1, an odd width, and i64, with independently narrower and wider results.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i2, i2, i64, i32, i2, i2, i64, i64, i2, i2)}> ({
    %one1 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %zero1 = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    %min3 = "llvm.mlir.constant"() <{value = -4 : i3}> : () -> i3
    %max3 = "llvm.mlir.constant"() <{value = 3 : i3}> : () -> i3
    %min64 = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %max64 = "llvm.mlir.constant"() <{value = 9223372036854775807 : i64}> : () -> i64

    %s1 = "llvm.intr.scmp"(%one1, %zero1) : (i1, i1) -> i2
    %u1 = "llvm.intr.ucmp"(%one1, %zero1) : (i1, i1) -> i2
    %s3 = "llvm.intr.scmp"(%min3, %max3) : (i3, i3) -> i64
    %u3 = "llvm.intr.ucmp"(%min3, %max3) : (i3, i3) -> i32
    %s64 = "llvm.intr.scmp"(%min64, %max64) : (i64, i64) -> i2
    %u64 = "llvm.intr.ucmp"(%min64, %max64) : (i64, i64) -> i2
    %s64rev = "llvm.intr.scmp"(%max64, %min64) : (i64, i64) -> i64
    %u64rev = "llvm.intr.ucmp"(%max64, %min64) : (i64, i64) -> i64
    %seq = "llvm.intr.scmp"(%min64, %min64) : (i64, i64) -> i2
    %ueq = "llvm.intr.ucmp"(%max64, %max64) : (i64, i64) -> i2
    "func.return"(%s1, %u1, %s3, %u3, %s64, %u64, %s64rev, %u64rev, %seq, %ueq) : (i2, i2, i64, i32, i2, i2, i64, i64, i2, i2) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x3#2, 0x1#2, 0xffffffffffffffff#64, 0x00000001#32, 0x3#2, 0x1#2, 0x0000000000000001#64, 0xffffffffffffffff#64, 0x0#2, 0x0#2]
// ISEL: "riscv.slt"
// ISEL: "riscv.sltu"
