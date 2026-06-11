// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %a = "test.test"() <{first}> : () -> i32
  %a = "test.test"() <{second}> : () -> i32
}) : () -> ()

// CHECK:already-defined.mlir:5:3: error: value %a has already been defined
// CHECK-NEXT:  %a = "test.test"() <{second}> : () -> i32
// CHECK-NEXT:  ^
// CHECK-NEXT:already-defined.mlir:4:3: note: previously defined here
// CHECK-NEXT:  %a = "test.test"() <{first}> : () -> i32
// CHECK-NEXT:  ^
