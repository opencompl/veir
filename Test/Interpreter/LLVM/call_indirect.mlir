// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// ALIVE_EXEC: cannot cross-check this test: Alive2 does not execute the body of a callee.

// An indirect call calls the function that its first operand points to.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i8 (i8)>, sym_name = "foo"}> ({
  ^bb0(%a: i8):
    %c1 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %r = "llvm.add"(%a, %c1) : (i8, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %f = "llvm.mlir.addressof"() <{global_name = @foo}> : () -> !llvm.ptr
    %c41 = "llvm.mlir.constant"() <{value = 41 : i8}> : () -> i8
    %r = "llvm.call"(%f, %c41) <{op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x2a#8]
