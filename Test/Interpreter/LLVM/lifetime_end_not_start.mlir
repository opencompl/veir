// RUN: veir-interpret %s | filecheck %s

// Lifetime marks apply to a whole object, so they must name its start.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.getelementptr"(%p, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.lifetime.end"(%q) : (!llvm.ptr) -> ()
    "func.return"(%one) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
