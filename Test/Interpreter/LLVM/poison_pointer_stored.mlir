// RUN: veir-interpret %s | filecheck %s

// A poison pointer written to memory occupies eight poison bytes, so
// reading it back gives poison again and reading it as an integer does too.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %poison = "llvm.mlir.poison"() : () -> i64
    %p = "llvm.inttoptr"(%poison) : (i64) -> !llvm.ptr
    %slot = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%p, %slot) : (!llvm.ptr, !llvm.ptr) -> ()
    %back = "llvm.load"(%slot) : (!llvm.ptr) -> !llvm.ptr
    %asInt = "llvm.load"(%slot) : (!llvm.ptr) -> i64
    %v = "llvm.ptrtoint"(%back) : (!llvm.ptr) -> i64
    "func.return"(%v, %asInt) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, poison]
