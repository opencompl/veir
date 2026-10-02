// RUN: veir-opt %s --allow-unregistered-dialect -p=cse | filecheck %s
// RUN: %if mlir-opt %{ veir-opt %s --allow-unregistered-dialect -p=cse | mlir-opt --allow-unregistered-dialect -o /dev/null %}

// These isolated test operations are known to MLIR but unregistered in Veir.
// CSE must preserve their isolation when the output is read back by MLIR.
"builtin.module"() ({
  %outer = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
  "test.test"(%outer) : (i32) -> ()
  "test.isolated_regions"() ({
    %inner = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %duplicate = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "test.test"(%inner, %duplicate) : (i32, i32) -> ()

    // Known capturing operations do not introduce another CSE boundary.
    "test.test"() ({
      %nestedDuplicate = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
      "test.test"(%nestedDuplicate) : (i32) -> ()
    }) : () -> ()

    // A nested unknown operation does introduce another boundary.
    "test.isolated_one_region_op"() ({
      %nested = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
      "test.test"(%nested) : (i32) -> ()
    }) : () -> ()
    "test.test"() : () -> ()
  }, {
    // Each region of an unknown operation has its own scope.
    %sibling = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "test.test"(%sibling) : (i32) -> ()
  }) : () -> ()

  // Existing captures in an unknown operation remain legal, including its
  // own operands. The verifier must keep using definite isolation.
  "unknown.capturing"(%outer) ({
    "test.test"(%outer) : (i32) -> ()
  }) : (i32) -> ()
}) : () -> ()

// CHECK:      %[[OUTER:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT: "test.test"(%[[OUTER]]) : (i32) -> ()
// CHECK-NEXT: "test.isolated_regions"() ({
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: %[[INNER:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT: "test.test"(%[[INNER]], %[[INNER]]) : (i32, i32) -> ()
// CHECK-NEXT: "test.test"() ({
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: "test.test"(%[[INNER]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: "test.isolated_one_region_op"() ({
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: %[[NESTED:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT: "test.test"(%[[NESTED]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: "test.test"() : () -> ()
// CHECK-NEXT: }, {
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: %[[SIBLING:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT: "test.test"(%[[SIBLING]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: "unknown.capturing"(%[[OUTER]]) ({
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: "test.test"(%[[OUTER]]) : (i32) -> ()
// CHECK-NEXT: }) : (i32) -> ()
