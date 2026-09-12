// RUN: veir-interpret %s | filecheck %s

// C++ `operator new` and `operator delete` are modelled by their mangled names.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<ptr (i64)>, linkage = #llvm.linkage<external>, sym_name = "_Znwm"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "_ZdlPv"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %p = "llvm.call"(%eight) <{callee = @_Znwm, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "llvm.call"(%p) <{callee = @_ZdlPv, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000c#64]
