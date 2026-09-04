// RUN: veir-opt %s -p=cir-to-std,reconcile-cast | filecheck %s

"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>) -> !cir.int<s, 32>>, sym_name = "f"}> ({
  ^bb0(%a : !cir.int<s, 32>):
    %b = "cir.cast"(%a) <{kind = 28 : i32}> : (!cir.int<s, 32>) -> !cir.bool
    "cir.brcond"(%b, %a)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (!cir.bool, !cir.int<s, 32>) -> ()
  ^bb1(%x : !cir.int<s, 32>):
    "cir.br"(%x)[^bb3] : (!cir.int<s, 32>) -> ()
  ^bb2:
    "cir.unreachable"() : () -> ()
  ^bb3(%r : !cir.int<s, 32>):
    "cir.return"(%r) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// The function boundary is left alone: it belongs to `coerce-cir-function-boundaries`.
// CHECK:      "cir.func"() <{"function_type" = !cir.func<(!cir.int<s, 32>) -> !cir.int<s, 32>>, "sym_name" = "f"}> ({
// CHECK-NEXT: ^{{.*}}([[A:%.*]] : !cir.int<s, 32>):
// CHECK-NEXT: [[A0:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: [[ZERO:%.*]] = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT: [[COND:%.*]] = "arith.cmpi"([[A0]], [[ZERO]]) <{"predicate" = 1 : i64}> : (i32, i32) -> i1

// The forwarded operand is cast to the retyped block argument; the block arguments of the
// successors are already `i32`, so no cast survives inside them.
// CHECK-NEXT: [[A1:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: "cf.cond_br"([[COND]], [[A1]]) [^{{.*}}, ^{{.*}}] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
// CHECK-NEXT: ^{{.*}}([[X:%.*]] : i32):
// CHECK-NEXT: "cf.br"([[X]]) [^{{.*}}] : (i32) -> ()
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "llvm.unreachable"() : () -> ()
// CHECK-NEXT: ^{{.*}}([[R:%.*]] : i32):

// The result cast is kept for the still `cir`-typed `cir.return`.
// CHECK-NEXT: [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[R]]) : (i32) -> !cir.int<s, 32>
// CHECK-NEXT: "cir.return"([[RES]]) : (!cir.int<s, 32>) -> ()
// CHECK-NEXT: }) : () -> ()
