// RUN: veir-interpret %s | filecheck %s

// Objects are separated by guard bytes. An address forged into the gap after
// the first alloca decodes to a pointer past that object's end, so loading
// through it is UB rather than reading the neighbour.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %r = "builtin.unrealized_conversion_cast"(%p) : (!llvm.ptr) -> !riscv.reg
    %s = "riscv.addi"(%r) <{value = 10 : i12}> : (!riscv.reg) -> !riscv.reg
    %t = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> !llvm.ptr
    %v = "llvm.load"(%t) : (!llvm.ptr) -> i8
    "func.return"(%v) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
