// RUN: veir-opt %s --allow-unregistered-dialect | filecheck %s

// A value may be used in a block that appears, in file order, before the block
// that defines it, as long as the definition dominates the use in the CFG. The
// parser resolves such forward references rather than rejecting them.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
  ^bb0:
    "cf.br"() [^bb2] : () -> ()
  ^bb1:
    "test.test"(%v) : (i32) -> ()
    "func.return"() : () -> ()
  ^bb2:
    %v = "test.test"() : () -> i32
    "cf.br"() [^bb1] : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{{.*}}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         "cf.br"() [^[[DEF:.*]]] : () -> ()
// CHECK-NEXT:       ^[[USE:.*]]():
// CHECK-NEXT:         "test.test"(%[[V:.*]]) : (i32) -> ()
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:       ^[[DEF]]():
// CHECK-NEXT:         %[[V]] = "test.test"() : () -> i32
// CHECK-NEXT:         "cf.br"() [^[[USE]]] : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
