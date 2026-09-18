// RUN: veir-interpret %s | filecheck %s

// Passing null to a `llvm.nonnull` argument is UB.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "foo"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %null = "llvm.mlir.zero"() : () -> !llvm.ptr
    "llvm.call"(%null) <{callee = @foo, arg_attrs = [{llvm.nonnull}], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    "func.return"(%zero) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
