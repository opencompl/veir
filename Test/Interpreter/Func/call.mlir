// RUN: veir-interpret %s | filecheck %s

// A direct call passes its operands to the callee and binds the value it returns.

"builtin.module"() ({
  "func.func"() <{sym_name = "foo", function_type = (i32) -> i32}> ({
  ^bb0(%a: i32):
    %r = "arith.addi"(%a, %a) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %c21 = "arith.constant"() <{value = 21 : i32}> : () -> i32
    %r = "func.call"(%c21) <{callee = @foo}> : (i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32]
