// RUN: veir-interpret %s | filecheck %s

// An object is laid out at the alignment its allocation declares, so the low
// bits of its address are clear.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %mask = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{alignment = 64 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %a = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    %low = "llvm.and"(%a, %mask) : (i64, i64) -> i64
    "func.return"(%low) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
