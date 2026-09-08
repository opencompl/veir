// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i128, memref<i128>) -> (), sym_name = "f"}> ({
  ^bb0(%v: i128, %m: memref<i128>):
    "memref.store"(%v, %m) <{nontemporal = true}> : (i128, memref<i128>) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: memref.store: expected no properties, but got 1 property: nontemporal
