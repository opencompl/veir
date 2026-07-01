// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64)}> ({
    // 0x40000000 + 0x40000000 = 0x80000000 -- so bit 31  is set such that sext != zext.
    %a = "llvm.mlir.constant"() <{value = 0x40000000 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 0x40000000 : i32}> : () -> i32
    %z = "llvm.add"(%a, %b) : (i32, i32) -> i32
    %zs = "llvm.sext"(%z) : (i32) -> i64
    %zz = "llvm.zext"(%z) : (i32) -> i64
    // 0x10 + 0x20 = 0x30 -- so bit 31 clear, sext == zext.
    %c = "llvm.mlir.constant"() <{value = 0x10 : i32}> : () -> i32
    %d = "llvm.mlir.constant"() <{value = 0x20 : i32}> : () -> i32
    %w = "llvm.add"(%c, %d) : (i32, i32) -> i32
    %ws = "llvm.sext"(%w) : (i32) -> i64
    %wz = "llvm.zext"(%w) : (i32) -> i64
    "func.return"(%zs, %zz, %ws, %wz) : (i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xffffffff80000000#64, 0x0000000080000000#64, 0x0000000000000030#64, 0x0000000000000030#64]
// CHECK:    "riscv.addw"
// CHECK:    "riscv.sextw"
// CHECK:    "riscv.zextw"
// CHECK:    Program output: #[0xffffffff80000000#64, 0x0000000080000000#64, 0x0000000000000030#64, 0x0000000000000030#64]
