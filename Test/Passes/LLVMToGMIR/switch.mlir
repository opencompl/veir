// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// Empty switches branch directly, forwarding the default arguments.
// CHECK: "sym_name" = "empty"
// CHECK: ^{{.*}}(%[[X:[a-z0-9_]+]] : i32, %[[D:[a-z0-9_]+]] : i64):
// CHECK-NEXT: "gmir.g_br"(%[[D]]) [^[[DEFAULT:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT: ^[[DEFAULT]](%{{.*}} : i64):
// CHECK-NEXT: "llvm.return"

// Each case is tested in source order, at the original width. The two adjacent cases that
// share a destination still forward their different arguments. The last false edge is default.
// CHECK: "sym_name" = "chain"
// CHECK: ^{{.*}}(%[[KEY:[a-z0-9_]+]] : i8, %[[A:[a-z0-9_]+]] : i64, %[[B:[a-z0-9_]+]] : i64):
// CHECK-NEXT: %[[K0:[a-z0-9_]+]] = "gmir.g_constant"() <{"value" = 5 : i8}>
// CHECK-NEXT: %[[C0:[a-z0-9_]+]] = "gmir.g_icmp"(%[[KEY]], %[[K0]]) <{"predicate" = 0 : i64}> : (i8, i8) -> i1
// CHECK-NEXT: "gmir.g_brcond"(%[[C0]], %[[A]], %[[B]]) [^[[CASE:[0-9]+]], ^[[NEXT0:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 2, 0>}>
// CHECK-NEXT: ^[[NEXT0]]():
// CHECK-NEXT: %[[K1:[a-z0-9_]+]] = "gmir.g_constant"() <{"value" = 6 : i8}>
// CHECK-NEXT: %[[C1:[a-z0-9_]+]] = "gmir.g_icmp"(%[[KEY]], %[[K1]]) <{"predicate" = 0 : i64}>
// CHECK-NEXT: "gmir.g_brcond"(%[[C1]], %[[B]], %[[A]]) [^[[CASE]], ^[[NEXT1:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 2, 0>}>
// CHECK-NEXT: ^[[NEXT1]]():
// CHECK-NEXT: %[[K2:[a-z0-9_]+]] = "gmir.g_constant"() <{"value" = -1 : i8}>
// CHECK-NEXT: %[[C2:[a-z0-9_]+]] = "gmir.g_icmp"(%[[KEY]], %[[K2]]) <{"predicate" = 0 : i64}>
// CHECK-NEXT: "gmir.g_brcond"(%[[C2]], %[[A]], %[[A]], %[[B]], %[[B]]) [^[[CASE]], ^[[CASE]]] <{"operandSegmentSizes" = array<i32: 1, 2, 2>}>
// CHECK-NEXT: ^[[CASE]](%{{.*}} : i64, %{{.*}} : i64):

// A switch in the last block appends its continuation blocks. A wide switch can be translated
// even when the target legalizer cannot handle its comparisons yet.
// CHECK: "sym_name" = "last_block"
// CHECK: "gmir.g_constant"() <{"value" = 18446744073709551616 : i128}>
// CHECK-NEXT: %{{.*}} = "gmir.g_icmp"({{.*}}) <{"predicate" = 0 : i64}> : (i128, i128) -> i1
// CHECK-NEXT: "gmir.g_brcond"
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: %{{.*}} = "gmir.g_constant"() <{"value" = -1 : i128}>
// CHECK-NEXT: %{{.*}} = "gmir.g_icmp"
// CHECK-NEXT: "gmir.g_brcond"

"builtin.module"() ({
  "llvm.func"() <{sym_name = "empty", function_type = !llvm.func<i64 (i32, i64)>}> ({
  ^entry(%x: i32, %d: i64):
    "llvm.switch"(%x, %d) [^default] <{case_operand_segments = array<i32>, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i32, i64) -> ()
  ^default(%r: i64):
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "chain", function_type = !llvm.func<i64 (i8, i64, i64)>}> ({
  ^entry(%key: i8, %a: i64, %b: i64):
    "llvm.switch"(%key, %b, %b, %a, %b, %b, %a, %a, %a) [^case, ^case, ^case, ^case]
      <{case_operand_segments = array<i32: 2, 2, 2>, case_values = dense<[5, 6, -1]> : vector<3xi8>,
        branch_weights = array<i32: 1, 1, 1, 100>, operandSegmentSizes = array<i32: 1, 2, 6>}>
      : (i8, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  ^case(%x: i64, %y: i64):
    %r = "llvm.sub"(%x, %y) : (i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "last_block", function_type = !llvm.func<i128 (i128)>}> ({
  ^entry(%x: i128):
    "llvm.br"() [^switch] : () -> ()
  ^exit:
    "llvm.return"(%x) : (i128) -> ()
  ^switch:
    "llvm.switch"(%x) [^exit, ^exit, ^exit]
      <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[18446744073709551616, -1]> : vector<2xi128>,
        operandSegmentSizes = array<i32: 1, 0, 0>}> : (i128) -> ()
  }) : () -> ()
}) : () -> ()
