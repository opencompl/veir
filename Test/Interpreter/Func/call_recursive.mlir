// RUN: veir-interpret --ctree %s | filecheck %s

// `sum(n) = n + sum(n - 1)` with `sum(0) = 0`, so `sum(2) = 3`. This only holds if each call keeps
// its own `%n` across the recursive call.
"builtin.module"() ({
  "func.func"() <{sym_name = "sum", function_type = (i32) -> i32}> ({
  ^entry(%n : i32):
    %zero = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %one = "arith.constant"() <{value = 1 : i32}> : () -> i32
    %done = "arith.cmpi"(%n, %zero) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "cf.cond_br"(%done) [^base, ^step] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^base:
    "func.return"(%zero) : (i32) -> ()
  ^step:
    %m = "arith.subi"(%n, %one) : (i32, i32) -> i32
    %s = "func.call"(%m) <{callee = @sum}> : (i32) -> i32
    %r = "arith.addi"(%n, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %two = "arith.constant"() <{value = 2 : i32}> : () -> i32
    %r = "func.call"(%two) <{callee = @sum}> : (i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32]
