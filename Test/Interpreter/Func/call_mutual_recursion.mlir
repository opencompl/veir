// RUN: veir-interpret %s | filecheck %s

// Functions can call each other: 7 is odd, as `is_odd` and `is_even` count it down.

"builtin.module"() ({
  "func.func"() <{sym_name = "is_even", function_type = (i32) -> i1}> ({
  ^bb0(%n: i32):
    %c0 = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %isZero = "arith.cmpi"(%n, %c0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "cf.cond_br"(%isZero) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    %true = "arith.constant"() <{value = 1 : i1}> : () -> i1
    "func.return"(%true) : (i1) -> ()
  ^bb2:
    %c1 = "arith.constant"() <{value = 1 : i32}> : () -> i32
    %m = "arith.subi"(%n, %c1) : (i32, i32) -> i32
    %r = "func.call"(%m) <{callee = @is_odd}> : (i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "is_odd", function_type = (i32) -> i1}> ({
  ^bb0(%n: i32):
    %c0 = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %isZero = "arith.cmpi"(%n, %c0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "cf.cond_br"(%isZero) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    %false = "arith.constant"() <{value = 0 : i1}> : () -> i1
    "func.return"(%false) : (i1) -> ()
  ^bb2:
    %c1 = "arith.constant"() <{value = 1 : i32}> : () -> i32
    %m = "arith.subi"(%n, %c1) : (i32, i32) -> i32
    %r = "func.call"(%m) <{callee = @is_even}> : (i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i1}> ({
    %c7 = "arith.constant"() <{value = 7 : i32}> : () -> i32
    %r = "func.call"(%c7) <{callee = @is_odd}> : (i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1#1]
