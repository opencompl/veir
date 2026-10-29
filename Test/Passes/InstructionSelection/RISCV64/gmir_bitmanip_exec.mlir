// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t.gmir && veir-interpret %t.gmir | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,riscv' > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i8, i8, i8, i8, i32, i16, i32, i8)}> ({
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %x32_slot = "llvm.alloca"(%n) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %x32_c = "llvm.mlir.constant"() <{value = 0x00f0e100 : i32}> : () -> i32
    "llvm.store"(%x32_c, %x32_slot) : (i32, !llvm.ptr) -> ()
    %x32 = "llvm.load"(%x32_slot) : (!llvm.ptr) -> i32
    %x16_slot = "llvm.alloca"(%n) <{elem_type = i16}> : (i64) -> !llvm.ptr
    %x16_c = "llvm.mlir.constant"() <{value = 0x12f0 : i16}> : () -> i16
    "llvm.store"(%x16_c, %x16_slot) : (i16, !llvm.ptr) -> ()
    %x16 = "llvm.load"(%x16_slot) : (!llvm.ptr) -> i16
    %x8_slot = "llvm.alloca"(%n) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %x8_c = "llvm.mlir.constant"() <{value = 0x14 : i8}> : () -> i8
    "llvm.store"(%x8_c, %x8_slot) : (i8, !llvm.ptr) -> ()
    %x8 = "llvm.load"(%x8_slot) : (!llvm.ptr) -> i8
    %zero8_slot = "llvm.alloca"(%n) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %zero8_c = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    "llvm.store"(%zero8_c, %zero8_slot) : (i8, !llvm.ptr) -> ()
    %zero8 = "llvm.load"(%zero8_slot) : (!llvm.ptr) -> i8
    %ctlz32 = "llvm.intr.ctlz"(%x32) <{is_zero_poison = false}> : (i32) -> i32
    %cttz32 = "llvm.intr.cttz"(%x32) <{is_zero_poison = false}> : (i32) -> i32
    %ctpop32 = "llvm.intr.ctpop"(%x32) : (i32) -> i32
    %ctlz8 = "llvm.intr.ctlz"(%x8) <{is_zero_poison = false}> : (i8) -> i8
    %cttz8 = "llvm.intr.cttz"(%x8) <{is_zero_poison = false}> : (i8) -> i8
    // A zero operand counts its full width.
    %ctlz8_zero = "llvm.intr.ctlz"(%zero8) <{is_zero_poison = false}> : (i8) -> i8
    %cttz8_zero = "llvm.intr.cttz"(%zero8) <{is_zero_poison = false}> : (i8) -> i8
    %bswap32 = "llvm.intr.bswap"(%x32) : (i32) -> i32
    %bswap16 = "llvm.intr.bswap"(%x16) : (i16) -> i16
    %bitreverse32 = "llvm.intr.bitreverse"(%x32) : (i32) -> i32
    %bitreverse8 = "llvm.intr.bitreverse"(%x8) : (i8) -> i8
    "func.return"(%ctlz32, %cttz32, %ctpop32, %ctlz8, %cttz8, %ctlz8_zero, %cttz8_zero, %bswap32, %bswap16, %bitreverse32, %bitreverse8) : (i32, i32, i32, i8, i8, i8, i8, i32, i16, i32, i8) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000008#32, 0x00000008#32, 0x00000008#32, 0x03#8, 0x02#8, 0x08#8, 0x08#8, 0x00e1f000#32, 0xf012#16, 0x00870f00#32, 0x28#8]
// CHECK:    "riscv.clzw"
// CHECK:    "riscv.ctzw"
// CHECK:    "riscv.cpopw"
// CHECK:    "riscv.clzw"
// CHECK:    "riscv.ctzw"
// CHECK:    "riscv.rev8"
// CHECK:    "riscv.rev8"
// CHECK:    "riscv.brev8"
// CHECK:    "riscv.rev8"
// CHECK:    "riscv.brev8"
// CHECK:    Program output: #[0x00000008#32, 0x00000008#32, 0x00000008#32, 0x03#8, 0x02#8, 0x08#8, 0x08#8, 0x00e1f000#32, 0xf012#16, 0x00870f00#32, 0x28#8]
