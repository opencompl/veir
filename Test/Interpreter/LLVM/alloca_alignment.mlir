// RUN: veir-interpret %s | filecheck %s

// An alloca with a large alignment lands at an address that honours it.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{alignment = 64 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    %a = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    "func.return"(%a) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000010040#64]
