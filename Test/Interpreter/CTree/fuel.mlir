// RUN: not veir-interpret --ctree --fuel=20 %s 2>&1 | filecheck %s
// CHECK: CTree interpreter exhausted its fuel
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
  ^entry:
    "cf.br"()[^loop] : () -> ()
  ^loop:
    "cf.br"()[^loop] : () -> ()
  }) : () -> ()
}) : () -> ()
