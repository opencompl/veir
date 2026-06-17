// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64)}> ({
    %1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
    %ptr = "llvm.alloca"(%1) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
    %6 = "llvm.load"(%ptr) : (!llvm.ptr) -> i64
    "llvm.store"(%1, %ptr) : (i64, !llvm.ptr) -> ()
    %7 = "llvm.load"(%ptr) : (!llvm.ptr) -> i64
    "llvm.store"(%6, %ptr) : (i64, !llvm.ptr) -> ()
    %8 = "llvm.load"(%ptr) : (!llvm.ptr) -> i64
    "func.return"(%6, %7, %8) : (i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, 0x0000000000000001#64, poison]
