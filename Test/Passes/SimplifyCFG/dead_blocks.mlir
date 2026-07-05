// RUN: veir-opt %s -p=simplify-cfg | filecheck %s

"builtin.module"() ({
  "func.func"() <{"function_type" = (i32) -> (), "sym_name" = "dead_block_with_args"}> ({
    ^entry(%x : i32):
      "cf.br"(%x) [^live] : (i32) -> ()
    ^dead(%y : i32):
      %c = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
      "test.test"(%y) : (i32) -> ()
      "cf.br"(%c) [^live] : (i32) -> ()
    ^live(%z : i32):
      "test.test"(%z) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{"function_type" = () -> (), "sym_name" = "keep_entry"}> ({
    ^entry():
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32) -> (), "sym_name" = "dead_block_with_args"}> ({
// CHECK-NEXT:   ^{{.*}}(%[[X:.*]] : i32):
// CHECK-NEXT:     "test.test"(%[[X]]) : (i32) -> ()
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "arith.constant"
// CHECK-NOT:      "cf.br"
// CHECK:      }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = () -> (), "sym_name" = "keep_entry"}> ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK:      }) : () -> ()
