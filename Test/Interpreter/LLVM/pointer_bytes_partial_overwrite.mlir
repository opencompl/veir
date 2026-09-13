// RUN: veir-interpret %s | filecheck %s

// Overwriting one byte of a stored pointer leaves a mix of pointer fragments
// and value bytes. Loading a pointer from it yields a poison pointer, and a
// load through that is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %zero8 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %b = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %b) : (!llvm.ptr, !llvm.ptr) -> ()
    %b3 = "llvm.getelementptr"(%b, %three) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%zero8, %b3) : (i8, !llvm.ptr) -> ()
    %p = "llvm.load"(%b) : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
