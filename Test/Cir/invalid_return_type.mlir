// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.return operand 0 type does not match the function's declared result type
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "f"}> ({
    %0 = "cir.const"() <{value = #cir.int<1> : !cir.int<u, 32>}> : () -> !cir.int<u, 32>
    "cir.return"(%0) : (!cir.int<u, 32>) -> ()
  }) : () -> ()
}) : () -> ()
