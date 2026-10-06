// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// ALIVE_EXEC: cannot cross-check this test: Alive2 does not execute the body of a callee.

// The caller sees the stores of a callee that returns nothing.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr)>, sym_name = "foo"}> ({
  ^bb0(%p: !llvm.ptr):
    %c42 = "llvm.mlir.constant"() <{value = 42 : i8}> : () -> i8
    "llvm.store"(%c42, %p) : (i8, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%c1) <{elem_type = i8}> : (i64) -> !llvm.ptr
    "llvm.call"(%p) <{callee = @foo, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x2a#8]
