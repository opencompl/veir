// RUN: not veir-interpret %s 2>&1 | filecheck %s
// NO_CROSS_CHECK: we expect an error

// A call with operand bundles cannot be interpreted, as the interpreter does not model them.
// TODO: Support operand bundles

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i8 (i8)>, sym_name = "foo"}> ({
  ^bb0(%a: i8):
    "llvm.return"(%a) : (i8) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %c1 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %r = "llvm.call"(%c1, %c1) <{callee = @foo, op_bundle_sizes = array<i32: 1>, op_bundle_tags = ["align"], operandSegmentSizes = array<i32: 1, 1>}> : (i8, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: call_operand_bundle.mlir:13:5: error: failed to interpret operation
