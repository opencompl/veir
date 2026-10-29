// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='llvm-to-gmir,legalize-riscv64,canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize{sccp=false},riscv-combine,isel-abi-riscv64,reconcile-cast,dce' > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64)}> ({
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    // 0x40000000 + 0x40000000 = 0x80000000 -- so bit 31  is set such that sext != zext.
    %a_slot = "llvm.alloca"(%n) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %a_c = "llvm.mlir.constant"() <{value = 0x40000000 : i32}> : () -> i32
    "llvm.store"(%a_c, %a_slot) : (i32, !llvm.ptr) -> ()
    %a = "llvm.load"(%a_slot) : (!llvm.ptr) -> i32
    %b = "llvm.mlir.constant"() <{value = 0x40000000 : i32}> : () -> i32
    %z = "llvm.add"(%a, %b) : (i32, i32) -> i32
    %zs = "llvm.sext"(%z) : (i32) -> i64
    %zz = "llvm.zext"(%z) : (i32) -> i64
    // 0x10 + 0x20 = 0x30 -- so bit 31 clear, sext == zext.
    %c_slot = "llvm.alloca"(%n) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %c_c = "llvm.mlir.constant"() <{value = 0x10 : i32}> : () -> i32
    "llvm.store"(%c_c, %c_slot) : (i32, !llvm.ptr) -> ()
    %c = "llvm.load"(%c_slot) : (!llvm.ptr) -> i32
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
