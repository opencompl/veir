// RUN: veir-interpret %s | filecheck %s

// A stored pointer reads back as an integer: its physical address. `@main`
// is object 1 at 0x10000, and the first alloca follows at 0x10010.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %b = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %b) : (!llvm.ptr, !llvm.ptr) -> ()
    %v = "llvm.load"(%b) : (!llvm.ptr) -> i64
    "func.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000010010#64]
