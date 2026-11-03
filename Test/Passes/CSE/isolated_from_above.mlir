// RUN: veir-opt %s -p=cse | filecheck %s

// CSE must not reuse a value defined outside an IsolatedFromAbove operation.
// In particular, the module-level constant cannot replace the identical
// constant inside llvm.func.

"builtin.module"() ({
  %outer = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "f"}> ({
  ^entry:
    %inner = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "test.test"(%inner) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[OUTER:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK:      "llvm.func"()
// CHECK:      %[[INNER:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT: "test.test"(%[[INNER]]) : (i32) -> ()
