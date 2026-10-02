// RUN: veir-opt %s | filecheck %s

// An unreachable predecessor of a reachable block may have a placeholder
// dominator fact used for dependency tracking. That must not make the block
// reachable and subject its deliberately unordered definitions to SSA
// dominance checks.

"func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^entry:
  "cf.br"() [^exit] : () -> ()
^dead:
  %y = "arith.addi"(%x, %x) : (i32, i32) -> i32
  %x = "arith.constant"() <{value = 1 : i32}> : () -> i32
  "cf.br"() [^exit] : () -> ()
^exit:
  "func.return"() : () -> ()
}) : () -> ()

// CHECK: func.func @f()
// CHECK: "arith.addi"
// CHECK: "arith.constant"
