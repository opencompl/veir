// RUN: veir-opt %s -p=cir-to-std,reconcile-cast | filecheck %s

"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>>, sym_name = "f"}> ({
  ^bb0(%a : !cir.int<s, 32>, %b : !cir.int<u, 8>):
    %s = "cir.add"(%a, %a) <{no_signed_wrap, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %d = "cir.div"(%s, %a) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %u = "cir.div"(%b, %b) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %sh = "cir.shift"(%d, %b) : (!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>
    %lt = "cir.cmp"(%sh, %a) <{kind = 0 : i32}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.bool
    %ult = "cir.cmp"(%u, %b) <{kind = 0 : i32}> : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.bool
    %sel = "cir.select"(%lt, %sh, %a) : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%sel) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// The function boundary is left alone: it belongs to `coerce-cir-function-boundaries`.
// CHECK:      "cir.func"() <{"function_type" = !cir.func<(!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>>, "sym_name" = "f"}> ({
// CHECK-NEXT: ^{{.*}}([[A:%.*]] : !cir.int<s, 32>, [[B:%.*]] : !cir.int<u, 8>):

// The argument casts are kept; the casts between lowered operations are reconciled away.
// CHECK-NEXT: [[A0:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: [[A1:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: [[SUM:%.*]] = "arith.addi"([[A0]], [[A1]]) : (i32, i32) -> i32
// CHECK-NEXT: [[A2:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: [[DIV:%.*]] = "arith.divsi"([[SUM]], [[A2]]) : (i32, i32) -> i32
// CHECK-NEXT: [[B0:%.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (!cir.int<u, 8>) -> i8
// CHECK-NEXT: [[AMT:%.*]] = "arith.extui"([[B0]]) : (i8) -> i32
// CHECK-NEXT: [[SHR:%.*]] = "arith.shrsi"([[DIV]], [[AMT]]) : (i32, i32) -> i32
// CHECK-NEXT: [[A3:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: [[LT:%.*]] = "arith.cmpi"([[SHR]], [[A3]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT: [[A4:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: [[SEL:%.*]] = "arith.select"([[LT]], [[SHR]], [[A4]]) : (i1, i32, i32) -> i32

// The result cast is kept for the still `cir`-typed `cir.return`.
// CHECK-NEXT: [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[SEL]]) : (i32) -> !cir.int<s, 32>
// CHECK-NEXT: "cir.return"([[RES]]) : (!cir.int<s, 32>) -> ()
// CHECK-NEXT: }) : () -> ()
