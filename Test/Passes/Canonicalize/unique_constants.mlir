// RUN: veir-opt %s -p=canonicalize | filecheck %s
// RUN: veir-opt %s -p='canonicalize{unique-constants=false}' | filecheck %s --check-prefix=OFF

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "hoist"}> ({
  ^entry(%x : i32):
    "test.test"(%x) : (i32) -> ()
    %one = "arith.constant"() <{value = 1 : i32}> : () -> i32
    "test.test"(%one) : (i32) -> ()
    "test.test"() ({
      %one_a = "arith.constant"() <{value = 1 : i32}> : () -> i32
      %two = "arith.constant"() <{value = 2 : i32}> : () -> i32
      "test.test"(%one_a, %two) : (i32, i32) -> ()
    }, {
      %one_b = "arith.constant"() <{value = 1 : i32}> : () -> i32
      "test.test"(%one_b) : (i32) -> ()
    }) : () -> ()
    "cf.br"() [^later] : () -> ()
  ^later:
    %two_c = "arith.constant"() <{value = 2 : i32}> : () -> i32
    "test.test"(%two_c) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: func.func @hoist
  // CHECK-NEXT:  %[[ONE:.*]] = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
  // CHECK-NEXT:  %[[TWO:.*]] = "arith.constant"() <{"value" = 2 : i32}> : () -> i32
  // CHECK-NEXT:  "test.test"(%{{.*}}) : (i32) -> ()
  // CHECK-NEXT:  "test.test"(%[[ONE]]) : (i32) -> ()
  // CHECK-NEXT:  "test.test"() ({
  // CHECK-NEXT:  ^{{[0-9]+}}():
  // CHECK-NEXT:    "test.test"(%[[ONE]], %[[TWO]]) : (i32, i32) -> ()
  // CHECK-NEXT:  }, {
  // CHECK-NEXT:  ^{{[0-9]+}}():
  // CHECK-NEXT:    "test.test"(%[[ONE]]) : (i32) -> ()
  // CHECK-NEXT:  }) : () -> ()
  // CHECK-NEXT:  "cf.br"() [^[[LATER:.*]]] : () -> ()
  // CHECK-NEXT:  ^[[LATER]]():
  // CHECK-NEXT:    "test.test"(%[[TWO]]) : (i32) -> ()

  // OFF-LABEL:   func.func @hoist
  // OFF-NEXT:    "test.test"(%{{.*}}) : (i32) -> ()
  // OFF-NEXT:    %{{.*}} = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
  // OFF-COUNT-2: "arith.constant"() <{"value" = 1 : i32}>
  // OFF-LABEL:   func.func @distinct

  // Constants that differ in opcode, type, or value stay separate, and a
  // constant already at the front of its entry block stays where it is.
  "func.func"() <{function_type = () -> (), sym_name = "distinct"}> ({
    %a = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %b = "arith.constant"() <{value = 0 : i64}> : () -> i64
    %c = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %d = "arith.constant"() <{value = 0 : i32}> : () -> i32
    "test.test"(%a, %b, %c, %d) : (i32, i64, i32, i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: func.func @distinct
  // CHECK-NEXT:  %[[A:.*]] = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
  // CHECK-NEXT:  %[[B:.*]] = "arith.constant"() <{"value" = 0 : i64}> : () -> i64
  // CHECK-NEXT:  %[[C:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
  // CHECK-NEXT:  "test.test"(%[[A]], %[[B]], %[[C]], %[[A]]) : (i32, i64, i32, i32) -> ()

  // Each function is its own isolated scope, so it keeps its own copy.
  "func.func"() <{function_type = () -> i32, sym_name = "other_scope"}> ({
    %one = "arith.constant"() <{value = 1 : i32}> : () -> i32
    "func.return"(%one) : (i32) -> ()
  }) : () -> ()

  // CHECK-LABEL: func.func @other_scope
  // CHECK-NEXT:  %[[OWN:.*]] = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
  // CHECK-NEXT:  "func.return"(%[[OWN]]) : (i32) -> ()
}) : () -> ()
