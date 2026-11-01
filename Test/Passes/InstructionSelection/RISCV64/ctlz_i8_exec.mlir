// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

// An `i8` `ctlz` is widened to `i32`, which subtracts the 24 added leading zeros. The subtraction
// is legalized to a word operation on `i64`, so its result needs no `zext.w` when it is truncated
// back to `i8`.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %c = "llvm.intr.ctlz"(%x) <{is_zero_poison = false}> : (i8) -> i8
    "func.return"(%c) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:       Program output: #[0x07#8]
// CHECK:     "riscv.subw"
// CHECK-NOT: "riscv.zextw"
// CHECK:     Program output: #[0x07#8]
