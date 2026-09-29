// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// An i16 store of a negative value lands in the middle of an i64, and the i16
// load that reads it back is both sign- and zero-extended. `riscv.lh`
// sign-extends into the register, so the zero-extension must still clear the
// upper bits. The whole i64 is reloaded to check that `riscv.sh` wrote exactly
// two bytes.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %one = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
      %buf = "llvm.alloca"(%one) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      %init = "llvm.mlir.constant"() <{ "value" = 1234605616436508552 : i64 }> : () -> i64
      "llvm.store"(%init, %buf) : (i64, !llvm.ptr) -> ()
      %two = "llvm.mlir.constant"() <{ "value" = 2 : i64 }> : () -> i64
      %p = "llvm.getelementptr"(%buf, %two) <{ elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %half = "llvm.mlir.constant"() <{ "value" = -32767 : i16 }> : () -> i16
      "llvm.store"(%half, %p) : (i16, !llvm.ptr) -> ()
      %h = "llvm.load"(%p) : (!llvm.ptr) -> i16
      %s = "llvm.sext"(%h) : (i16) -> i64
      %z = "llvm.zext"(%h) : (i16) -> i64
      %whole = "llvm.load"(%buf) : (!llvm.ptr) -> i64
      %x = "llvm.xor"(%whole, %s) : (i64, i64) -> i64
      %thirtytwo = "llvm.mlir.constant"() <{ "value" = 32 : i64 }> : () -> i64
      %zs = "llvm.shl"(%z, %thirtytwo) : (i64, i64) -> i64
      %out = "llvm.add"(%x, %zs) : (i64, i64) -> i64
      "llvm.return"(%out) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// memory 0x1122334480017788 ^ sext 0xffffffffffff8001 = 0xeeddccbb7ffef789,
// plus zext << 32 = 0x0000800100000000.
// SRC: Program output: #[0xeede4cbc7ffef789#64]
// CHECK: Program output: #[0xeede4cbc7ffef789#64]

// ISEL: "riscv.sh"({{.*}}) <{"value" = 2 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// ISEL: "riscv.lh"({{.*}}) <{"value" = 2 : i64}> : (!riscv.reg) -> !riscv.reg
