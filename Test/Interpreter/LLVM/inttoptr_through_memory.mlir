// RUN: veir-interpret %s | filecheck %s

// An address stored as an integer and loaded back as a pointer denotes the
// object at that address, so the load through it succeeds.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 91 : i64}> : () -> i64
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %b = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %a) : (i64, !llvm.ptr) -> ()
    %addr = "llvm.ptrtoint"(%a) : (!llvm.ptr) -> i64
    "llvm.store"(%addr, %b) : (i64, !llvm.ptr) -> ()
    %p = "llvm.load"(%b) : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000005b#64]
