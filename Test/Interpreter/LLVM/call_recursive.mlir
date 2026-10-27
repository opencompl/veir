// RUN: veir-interpret %s | filecheck %s
// NO_CROSS_CHECK: llubi cannot run calls until veir2llvm translates `llvm.call`, and alive-exec does not run callees.
// TODO: Support calls in veir2llvm

// A function can call itself: the factorial of 5 is 120.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i8 (i8)>, sym_name = "foo"}> ({
  ^bb0(%n: i8):
    %c0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %c1 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %isZero = "llvm.icmp"(%n, %c0) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%isZero) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "llvm.return"(%c1) : (i8) -> ()
  ^bb2:
    %m = "llvm.sub"(%n, %c1) : (i8, i8) -> i8
    %f = "llvm.call"(%m) <{callee = @foo, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i8) -> i8
    %r = "llvm.mul"(%n, %f) : (i8, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %c5 = "llvm.mlir.constant"() <{value = 5 : i8}> : () -> i8
    %r = "llvm.call"(%c5) <{callee = @foo, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x78#8]
