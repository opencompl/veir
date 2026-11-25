// RUN: veir-interpret --ctree %s | filecheck %s

// `main` calls a function on two arguments, which must arrive in order: 2 - 1 = 1.
"builtin.module"() ({
  "func.func"() <{sym_name = "sub", function_type = (i32, i32) -> i32}> ({
  ^entry(%a : i32, %b : i32):
    %r = "arith.subi"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %one = "arith.constant"() <{value = 1 : i32}> : () -> i32
    %two = "arith.constant"() <{value = 2 : i32}> : () -> i32
    %r = "func.call"(%two, %one) <{callee = @sub}> : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32]
