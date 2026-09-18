// RUN: veir-interpret %s | filecheck %s

// The result of an unknown call is whatever the oracle picks: poison by default.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, linkage = #llvm.linkage<external>, sym_name = "foo"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %r = "llvm.call"() <{callee = @foo, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
