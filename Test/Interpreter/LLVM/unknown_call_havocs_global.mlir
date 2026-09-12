// RUN: veir-interpret %s | filecheck %s

// Globals are always reachable, so an unknown call may overwrite them,
// unless they are constant.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, constant, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "c", value = 42 : i32}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "foo"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32)}> ({
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %c = "llvm.mlir.addressof"() <{global_name = @c}> : () -> !llvm.ptr
    "llvm.call"() <{callee = @foo, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
    %vg = "llvm.load"(%g) : (!llvm.ptr) -> i32
    %vc = "llvm.load"(%c) : (!llvm.ptr) -> i32
    "func.return"(%vg, %vc) : (i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, 0x0000002a#32]
