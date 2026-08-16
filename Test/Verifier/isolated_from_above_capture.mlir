// RUN: not veir-opt %s 2>&1 | filecheck %s

// A `func.func` is IsolatedFromAbove, so an operation in its body may not use
// a value defined in an enclosing region.
"builtin.module"() ({
  "func.func"() <{sym_name = "outer", function_type = () -> ()}> ({
  ^bb0:
    %a = "test.test"() : () -> i1
    "func.func"() <{sym_name = "inner", function_type = () -> ()}> ({
    ^bb0:
      "test.test"(%a) : (i1) -> ()
      "func.return"() : () -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: operand uses a value defined outside the isolated region that encloses its use
