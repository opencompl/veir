// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

// An `i8` division is legalized to a word operation on `i64` that is truncated straight to `i8`,
// so its result needs no `zext.w` when it is returned.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    // 0xff
    %a = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    // Not a power of two, which would become a shift.
    %b = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %q = "llvm.udiv"(%a, %b) : (i8, i8) -> i8
    "func.return"(%q) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:       Program output: #[0x55#8]
// CHECK:     "riscv.divuw"
// CHECK-NOT: "riscv.zextw"
// CHECK:     Program output: #[0x55#8]
