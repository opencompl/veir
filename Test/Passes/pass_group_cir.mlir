// RUN: veir-opt %s -p=cir | filecheck %s

// The `cir` pass group lowers the `cir` integer core all the way to `arith`, `cf` and
// `llvm`: ops and branches are lowered, `cir` function boundaries are coerced to the
// builtin integer of the same width, and the resulting cast round trips are reconciled
// away. Only the `cir.func`/`cir.return` shell keeps its `cir` spelling.

"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>>, sym_name = "binops"}> ({
  ^bb0(%a : !cir.int<s, 32>, %b : !cir.int<u, 8>):
    %s = "cir.add"(%a, %a) <{no_signed_wrap, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %d = "cir.div"(%s, %a) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %sh = "cir.shift"(%d, %b) : (!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>
    %lt = "cir.cmp"(%sh, %a) <{kind = 0 : i32}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.bool
    %sel = "cir.select"(%lt, %sh, %a) : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%sel) : (!cir.int<s, 32>) -> ()
  }) : () -> ()

  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>) -> !cir.int<s, 32>>, sym_name = "branches"}> ({
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

// CHECK:      "cir.func"() <{"function_type" = !cir.func<(i32, i8) -> i32>, "sym_name" = "binops"}> ({
// CHECK-NEXT: ^{{.*}}([[A:%.*]] : i32, [[B:%.*]] : i8):
// CHECK-NEXT: [[SUM:%.*]] = "arith.addi"([[A]], [[A]]) : (i32, i32) -> i32
// CHECK-NEXT: [[DIV:%.*]] = "arith.divsi"([[SUM]], [[A]]) : (i32, i32) -> i32
// CHECK-NEXT: [[AMT:%.*]] = "arith.extui"([[B]]) : (i8) -> i32
// CHECK-NEXT: [[SHR:%.*]] = "arith.shrsi"([[DIV]], [[AMT]]) : (i32, i32) -> i32
// CHECK-NEXT: [[LT:%.*]] = "arith.cmpi"([[SHR]], [[A]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT: [[SEL:%.*]] = "arith.select"([[LT]], [[SHR]], [[A]]) : (i1, i32, i32) -> i32
// CHECK-NEXT: "cir.return"([[SEL]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()

// CHECK:      "cir.func"() <{"function_type" = !cir.func<(i32) -> i32>, "sym_name" = "branches"}> ({
// CHECK-NEXT: ^{{.*}}([[A:%.*]] : i32):
// CHECK-NEXT: [[ZERO:%.*]] = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT: [[COND:%.*]] = "arith.cmpi"([[A]], [[ZERO]]) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT: "cf.cond_br"([[COND]], [[A]]) [^{{.*}}, ^{{.*}}] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
// CHECK-NEXT: ^{{.*}}([[X:%.*]] : i32):
// CHECK-NEXT: "cf.br"([[X]]) [^{{.*}}] : (i32) -> ()
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "llvm.unreachable"() : () -> ()
// CHECK-NEXT: ^{{.*}}([[R:%.*]] : i32):
// CHECK-NEXT: "cir.return"([[R]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
