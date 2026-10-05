// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// ALIVE_EXEC: cannot cross-check this test: Alive2 does not execute the body of a callee.

// A direct call passes its operands to the callee and binds the value it returns.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i8 (i8, i8)>, sym_name = "foo"}> ({
  ^bb0(%a: i8, %b: i8):
    %r = "llvm.sub"(%a, %b) : (i8, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %c7 = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %r = "llvm.call"(%c7, %c2) <{callee = @foo, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i8, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x05#8]
