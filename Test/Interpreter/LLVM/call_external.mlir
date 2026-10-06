// RUN: not veir-interpret %s 2>&1 | filecheck %s

// A call to a function without a body cannot be interpreted.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "foo"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %r = "llvm.call"() <{callee = @foo, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: call_external.mlir:9:5: error: failed to interpret operation
