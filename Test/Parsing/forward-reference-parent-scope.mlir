// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "test.test"() ({
    ^inner:
      "test.test"(%a) : (i32) -> ()
      "cf.br"() [^inner] : () -> ()
    }) : () -> ()
    %a = "test.test"() : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{{.*}}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         "test.test"() ({
// CHECK-NEXT:           ^[[INNER:.*]]():
// CHECK-NEXT:             "test.test"(%[[A:.*]]) : (i32) -> ()
// CHECK-NEXT:             "cf.br"() [^[[INNER]]] : () -> ()
// CHECK-NEXT:         }) : () -> ()
// CHECK-NEXT:         %[[A]] = "test.test"() : () -> i32
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
