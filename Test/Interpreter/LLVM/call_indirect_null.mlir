// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// ALIVE_EXEC: cannot cross-check this test: Alive2 does not execute the body of a callee.

// Calling a pointer that does not point to a function is undefined behavior.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %f = "llvm.mlir.zero"() : () -> !llvm.ptr
    %r = "llvm.call"(%f) <{op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
