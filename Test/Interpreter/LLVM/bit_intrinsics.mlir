// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i16, i8)}> ({
    %x = "llvm.mlir.constant"() <{ "value" = 0x12 : i8 }> : () -> i8
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %wide = "llvm.mlir.constant"() <{ "value" = 0x1234 : i16 }> : () -> i16
    %ctlz = "llvm.intr.ctlz"(%x) <{is_zero_poison = false}> : (i8) -> i8
    %cttz = "llvm.intr.cttz"(%x) <{is_zero_poison = false}> : (i8) -> i8
    %ctpop = "llvm.intr.ctpop"(%x) : (i8) -> i8
    %ctlz_poison = "llvm.intr.ctlz"(%zero) <{is_zero_poison = true}> : (i8) -> i8
    %cttz_zero = "llvm.intr.cttz"(%zero) <{is_zero_poison = false}> : (i8) -> i8
    %bswap = "llvm.intr.bswap"(%wide) : (i16) -> i16
    %bitreverse = "llvm.intr.bitreverse"(%x) : (i8) -> i8
    "func.return"(%ctlz, %cttz, %ctpop, %ctlz_poison, %cttz_zero, %bswap, %bitreverse) : (i8, i8, i8, i8, i8, i16, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x03#8, 0x01#8, 0x02#8, poison, 0x08#8, 0x3412#16, 0x48#8]
