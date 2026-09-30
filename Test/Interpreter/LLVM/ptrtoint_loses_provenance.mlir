// RUN: veir-interpret %s | filecheck %s

// The same walk through `llvm.ptrtoint` and `llvm.inttoptr` instead of a bitcast. A register
// holds an address and nothing else, so the pointer that comes back is the one whose object
// contains that address -- here `%q`, not `%p`. Walking back from it leaves `%q`, and the
// access is out of bounds.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %k = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %mk = "llvm.mlir.constant"() <{value = -16 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    %past = "llvm.getelementptr"(%p, %k) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %addr = "llvm.ptrtoint"(%past) : (!llvm.ptr) -> i64
    %same = "llvm.inttoptr"(%addr) : (i64) -> !llvm.ptr
    %back = "llvm.getelementptr"(%same, %mk) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %res = "llvm.load"(%back) : (!llvm.ptr) -> i64
    "func.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
// CHECK: %res = "llvm.load"
