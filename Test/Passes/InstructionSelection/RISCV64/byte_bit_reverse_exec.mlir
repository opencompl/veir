// Exercise high bits at every width; composed intrinsics also retain their inner results.
// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv > %t
// RUN: veir-interpret %t | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i16, i16, i16, i16, i32, i32, i32, i32, i64, i64, i64, i64, i16, i16, i32, i32, i64, i64)}> ({
    %x8 = "llvm.mlir.constant"() <{value = 131 : i8}> : () -> i8
    %bitreverse_x_8 = "llvm.intr.bitreverse"(%x8) : (i8) -> i8
    %x16 = "llvm.mlir.constant"() <{value = 50563 : i16}> : () -> i16
    %bswap_x_16 = "llvm.intr.bswap"(%x16) : (i16) -> i16
    %bitreverse_x_16 = "llvm.intr.bitreverse"(%x16) : (i16) -> i16
    %inner_bswap_bitreverse_16 = "llvm.intr.bitreverse"(%x16) : (i16) -> i16
    %bswap_bitreverse_16 = "llvm.intr.bswap"(%inner_bswap_bitreverse_16) : (i16) -> i16
    %inner_bitreverse_bswap_16 = "llvm.intr.bswap"(%x16) : (i16) -> i16
    %bitreverse_bswap_16 = "llvm.intr.bitreverse"(%inner_bitreverse_bswap_16) : (i16) -> i16
    %x32 = "llvm.mlir.constant"() <{value = 2166572419 : i32}> : () -> i32
    %bswap_x_32 = "llvm.intr.bswap"(%x32) : (i32) -> i32
    %bitreverse_x_32 = "llvm.intr.bitreverse"(%x32) : (i32) -> i32
    %inner_bswap_bitreverse_32 = "llvm.intr.bitreverse"(%x32) : (i32) -> i32
    %bswap_bitreverse_32 = "llvm.intr.bswap"(%inner_bswap_bitreverse_32) : (i32) -> i32
    %inner_bitreverse_bswap_32 = "llvm.intr.bswap"(%x32) : (i32) -> i32
    %bitreverse_bswap_32 = "llvm.intr.bitreverse"(%inner_bitreverse_bswap_32) : (i32) -> i32
    %x64 = "llvm.mlir.constant"() <{value = 9920249030613616003 : i64}> : () -> i64
    %bswap_x_64 = "llvm.intr.bswap"(%x64) : (i64) -> i64
    %bitreverse_x_64 = "llvm.intr.bitreverse"(%x64) : (i64) -> i64
    %inner_bswap_bitreverse_64 = "llvm.intr.bitreverse"(%x64) : (i64) -> i64
    %bswap_bitreverse_64 = "llvm.intr.bswap"(%inner_bswap_bitreverse_64) : (i64) -> i64
    %inner_bitreverse_bswap_64 = "llvm.intr.bswap"(%x64) : (i64) -> i64
    %bitreverse_bswap_64 = "llvm.intr.bitreverse"(%inner_bitreverse_bswap_64) : (i64) -> i64
    "func.return"(%bitreverse_x_8, %bswap_x_16, %bitreverse_x_16, %bswap_bitreverse_16, %bitreverse_bswap_16, %bswap_x_32, %bitreverse_x_32, %bswap_bitreverse_32, %bitreverse_bswap_32, %bswap_x_64, %bitreverse_x_64, %bswap_bitreverse_64, %bitreverse_bswap_64, %inner_bswap_bitreverse_16, %inner_bitreverse_bswap_16, %inner_bswap_bitreverse_32, %inner_bitreverse_bswap_32, %inner_bswap_bitreverse_64, %inner_bitreverse_bswap_64) : (i8, i16, i16, i16, i16, i32, i32, i32, i32, i64, i64, i64, i64, i16, i16, i32, i32, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xc1#8, 0x83c5#16, 0xc1a3#16, 0xa3c1#16, 0xa3c1#16, 0x83452381#32, 0xc1a2c481#32, 0x81c4a2c1#32, 0x81c4a2c1#32, 0x83452301efcdab89#64, 0xc1a2c480f7b3d591#64, 0x91d5b3f780c4a2c1#64, 0x91d5b3f780c4a2c1#64, 0xc1a3#16, 0x83c5#16, 0xc1a2c481#32, 0x83452381#32, 0xc1a2c480f7b3d591#64, 0x83452301efcdab89#64]
