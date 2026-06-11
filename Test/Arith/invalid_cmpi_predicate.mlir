// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0():
  %a = "arith.constant"() <{"value" = 13 : i32}> : () -> i32
  %b = "arith.constant"() <{"value" = 3 : i32}> : () -> i32
  %r = "arith.cmpi"(%a, %b) <{"predicate" = 10 : i64}> : (i32, i32) -> i1
}) : () -> ()

// CHECK: arith.cmpi: invalid predicate 10
