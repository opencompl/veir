// RUN: veir-interpret %s | filecheck %s

// An object whose address never escaped cannot be reached by an unknown
// call, so its contents survive the call.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "foo"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %a) : (i64, !llvm.ptr) -> ()
    "llvm.call"() <{callee = @foo, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
    %r = "llvm.load"(%a) : (!llvm.ptr) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000005#64]
