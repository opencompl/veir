// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t.gmir && veir-interpret %t.gmir | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,riscv' > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i8, i8, i8, i8, i32, i32, i8, i8, i32, i16, i32, i8)}> ({
    %x32 = "llvm.mlir.constant"() <{value = 0x00f0e100 : i32}> : () -> i32
    %x16 = "llvm.mlir.constant"() <{value = 0x12f0 : i16}> : () -> i16
    %x8 = "llvm.mlir.constant"() <{value = 0x14 : i8}> : () -> i8
    %zero8 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %ctlz32 = "llvm.intr.ctlz"(%x32) <{is_zero_poison = false}> : (i32) -> i32
    %cttz32 = "llvm.intr.cttz"(%x32) <{is_zero_poison = false}> : (i32) -> i32
    %ctpop32 = "llvm.intr.ctpop"(%x32) : (i32) -> i32
    %ctlz8 = "llvm.intr.ctlz"(%x8) <{is_zero_poison = false}> : (i8) -> i8
    %cttz8 = "llvm.intr.cttz"(%x8) <{is_zero_poison = false}> : (i8) -> i8
    // A zero operand counts its full width.
    %ctlz8_zero = "llvm.intr.ctlz"(%zero8) <{is_zero_poison = false}> : (i8) -> i8
    %cttz8_zero = "llvm.intr.cttz"(%zero8) <{is_zero_poison = false}> : (i8) -> i8
    // Counts whose zero input is poison agree with the defined counts on a non-zero operand.
    %ctlz32_zp = "llvm.intr.ctlz"(%x32) <{is_zero_poison = true}> : (i32) -> i32
    %cttz32_zp = "llvm.intr.cttz"(%x32) <{is_zero_poison = true}> : (i32) -> i32
    %ctlz8_zp = "llvm.intr.ctlz"(%x8) <{is_zero_poison = true}> : (i8) -> i8
    %cttz8_zp = "llvm.intr.cttz"(%x8) <{is_zero_poison = true}> : (i8) -> i8
    %bswap32 = "llvm.intr.bswap"(%x32) : (i32) -> i32
    %bswap16 = "llvm.intr.bswap"(%x16) : (i16) -> i16
    %bitreverse32 = "llvm.intr.bitreverse"(%x32) : (i32) -> i32
    %bitreverse8 = "llvm.intr.bitreverse"(%x8) : (i8) -> i8
    "func.return"(%ctlz32, %cttz32, %ctpop32, %ctlz8, %cttz8, %ctlz8_zero, %cttz8_zero, %ctlz32_zp, %cttz32_zp, %ctlz8_zp, %cttz8_zp, %bswap32, %bswap16, %bitreverse32, %bitreverse8) : (i32, i32, i32, i8, i8, i8, i8, i32, i32, i8, i8, i32, i16, i32, i8) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000008#32, 0x00000008#32, 0x00000008#32, 0x03#8, 0x02#8, 0x08#8, 0x08#8, 0x00000008#32, 0x00000008#32, 0x03#8, 0x02#8, 0x00e1f000#32, 0xf012#16, 0x00870f00#32, 0x28#8]
// CHECK:    "riscv.clzw"
// CHECK:    "riscv.ctzw"
// CHECK:    "riscv.cpopw"
// CHECK:    "riscv.clzw"
// CHECK:    "riscv.ctzw"
// CHECK:    "riscv.clzw"
// CHECK:    "riscv.ctzw"
// CHECK:    "riscv.rev8"
// CHECK:    "riscv.rev8"
// CHECK:    "riscv.brev8"
// CHECK:    "riscv.rev8"
// CHECK:    "riscv.brev8"
// CHECK:    Program output: #[0x00000008#32, 0x00000008#32, 0x00000008#32, 0x03#8, 0x02#8, 0x08#8, 0x08#8, 0x00000008#32, 0x00000008#32, 0x03#8, 0x02#8, 0x00e1f000#32, 0xf012#16, 0x00870f00#32, 0x28#8]
