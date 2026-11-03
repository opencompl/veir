// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// The store of `store_misaligned.mlir` with `alignment = 1`: the attribute
// lowers the requirement, so the store is allowed, and a load with the same
// attribute reads the i32 back.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %p2 = "llvm.getelementptr"(%p, %two) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %p2) <{alignment = 1 : i64}> : (i32, !llvm.ptr) -> ()
    %r = "llvm.load"(%p2) <{alignment = 1 : i64}> : (!llvm.ptr) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000007#32]
