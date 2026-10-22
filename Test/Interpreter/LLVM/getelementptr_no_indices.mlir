// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// A `getelementptr` with no indices returns its base pointer.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    %q = "llvm.getelementptr"(%p) <{elem_type = i8, rawConstantIndices = array<i32>}> : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
