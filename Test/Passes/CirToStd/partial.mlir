// RUN: veir-opt %s --allow-unregistered-dialect -p=cir-to-std{strict=false},reconcile-cast | filecheck %s
// RUN: not veir-opt %s --allow-unregistered-dialect -p=cir-to-std 2>&1 | filecheck %s --check-prefix=STRICT

// With `strict=false`, cir-to-std lowers what it can and leaves the rest in place: the null
// pointer constant, the pointer comparison and the unknown `cir.call` survive, while the
// integer arithmetic around them is lowered and bridged with casts. The default strict mode
// rejects the same input.
// STRICT: cir-to-std: operation '{{.*}}' was not lowered

"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>, !cir.ptr<!cir.int<s, 32>>) -> !cir.int<s, 32>>, sym_name = "f"}> ({
  ^bb0(%a : !cir.int<s, 32>, %p : !cir.ptr<!cir.int<s, 32>>):
    %null = "cir.const"() <{value = #cir.ptr<null> : !cir.ptr<!cir.int<s, 32>>}> : () -> !cir.ptr<!cir.int<s, 32>>
    %isnull = "cir.cmp"(%p, %null) <{kind = 4 : i32}> : (!cir.ptr<!cir.int<s, 32>>, !cir.ptr<!cir.int<s, 32>>) -> !cir.bool
    %g = "cir.call"(%a) <{callee = @g}> : (!cir.int<s, 32>) -> !cir.int<s, 32>
    %s = "cir.add"(%a, %g) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %r = "cir.select"(%isnull, %s, %a) : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%r) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "cir.const"() <{"value" = #cir.ptr<null> : !cir.ptr<!cir.int<s, 32>>}> : () -> !cir.ptr<!cir.int<s, 32>>
// CHECK-NEXT: [[ISNULL:%.*]] = "cir.cmp"(%{{.*}}, %{{.*}}) <{"kind" = 4 : i32}> : (!cir.ptr<!cir.int<s, 32>>, !cir.ptr<!cir.int<s, 32>>) -> !cir.bool
// CHECK-NEXT: [[G:%.*]] = "cir.call"(%{{.*}}) <{"callee" = @g}> : (!cir.int<s, 32>) -> !cir.int<s, 32>
// CHECK:      [[G0:%.*]] = "builtin.unrealized_conversion_cast"([[G]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: [[SUM:%.*]] = "arith.addi"(%{{.*}}, [[G0]]) : (i32, i32) -> i32
// CHECK-NEXT: [[COND:%.*]] = "builtin.unrealized_conversion_cast"([[ISNULL]]) : (!cir.bool) -> i1
// CHECK:      "arith.select"([[COND]], [[SUM]], %{{.*}}) : (i1, i32, i32) -> i32
