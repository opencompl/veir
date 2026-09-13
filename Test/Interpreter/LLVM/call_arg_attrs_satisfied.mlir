// RUN: veir-interpret %s | filecheck %s

// All three attributes hold for an aligned, live, 8-byte alloca.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "foo"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.call"(%p) <{callee = @foo, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 8 : i64, llvm.nonnull}], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    "func.return"(%zero) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000#32]
