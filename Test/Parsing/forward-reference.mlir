// RUN: veir-opt %s --allow-unregistered-dialect | filecheck %s

// A value may be used in a block that appears, in file order, before the block
// that defines it, as long as the definition dominates the use in the CFG. The
// parser resolves such forward references rather than rejecting them.

"builtin.module"() ({
^bb0:
  "test.test"()[^bb2] : () -> ()
^bb1:
  "test.test"(%v) : (i32) -> ()
  "test.test"()[^bb1] : () -> ()
^bb2:
  %v = "test.test"() : () -> i32
  "test.test"()[^bb1] : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "test.test"() [^[[DEF:.*]]] : () -> ()
// CHECK-NEXT:   ^[[USE:.*]]():
// CHECK-NEXT:     "test.test"(%[[V:.*]]) : (i32) -> ()
// CHECK-NEXT:     "test.test"() [^[[USE]]] : () -> ()
// CHECK-NEXT:   ^[[DEF]]():
// CHECK-NEXT:     %[[V]] = "test.test"() : () -> i32
// CHECK-NEXT:     "test.test"() [^[[USE]]] : () -> ()
// CHECK-NEXT: }) : () -> ()
