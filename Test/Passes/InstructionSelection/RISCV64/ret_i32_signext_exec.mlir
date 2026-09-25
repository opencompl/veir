// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// The calling convention returns an `i32` sign-extended to 64 bits, so -1 comes
// back as all ones, not as 0x00000000ffffffff.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>, res_attrs = [{llvm.signext}]}> ({
    ^bb0():
      %x = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
      "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xffffffff#32]
// CHECK: Program output: #[0xffffffffffffffff#64]
