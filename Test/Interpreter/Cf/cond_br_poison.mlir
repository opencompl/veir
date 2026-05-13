// RUN: veir-interpret %s | filecheck %s

// Branching on a poison i1 in the cf dialect is undefined behaviour. The i1
// poison is produced by `arith.addi nuw` on i1 (1 + 1 overflows unsigned).
"builtin.module"() ({
  ^entry():
    %one    = "arith.constant"() <{"value" = 1 : i1}> : () -> i1
    %poison = "arith.addi"(%one, %one) <{nuw}> : (i1, i1) -> i1
    %tval   = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %fval   = "arith.constant"() <{"value" = 99 : i32}> : () -> i32
    "cf.cond_br"(%poison, %tval, %fval) [^t, ^f]
      <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^t(%x : i32):
    "func.return"(%x) : (i32) -> ()
  ^f(%y : i32):
    "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
