// RUN: veir-interpret %s | filecheck %s

// An `alignment` attribute larger than the type's natural alignment is
// checked too: an i8 store claiming 8-byte alignment at offset 1 is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 5 : i8}> : () -> i8
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.getelementptr"(%p, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %q) <{alignment = 8 : i64}> : (i8, !llvm.ptr) -> ()
    %r = "llvm.load"(%q) : (!llvm.ptr) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
