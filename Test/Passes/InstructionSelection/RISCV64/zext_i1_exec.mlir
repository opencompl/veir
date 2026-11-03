// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// Zero-extending an `i1` block argument, as clang does for `a && b`, gives 1 after lowering.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i8)}> ({
    ^bb0():
      %true = "llvm.mlir.constant"() <{value = true}> : () -> i1
      "llvm.br"(%true)[^bb1] : (i1) -> ()
    ^bb1(%x : i1):
      %x32 = "llvm.zext"(%x) : (i1) -> i32
      %x8 = "llvm.zext"(%x) : (i1) -> i8
      "func.return"(%x32, %x8) : (i32, i8) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000001#32, 0x01#8]
// CHECK: Program output: #[0x00000001#32, 0x01#8]
