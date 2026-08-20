// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// llvm.func is isolated from above just like func.func.

"builtin.module"() ({
  %v = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "f"}> ({
    "test.test"(%v) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: test.test: operand uses a value defined outside the isolated region
