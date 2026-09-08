// RUN: not veir-opt %s 2>&1 | filecheck %s

// As for memref.load: memref.store's optional `nontemporal` and `alignment`
// attributes are not modeled, so an operation carrying one is rejected instead
// of parsed into a store that means something else.

// CHECK: memref.store: expected no properties, but got 1 property: nontemporal
"builtin.module"() ({
  "func.func"() <{function_type = (i128, memref<i128>) -> (), sym_name = "f"}> ({
  ^bb0(%v: i128, %m: memref<i128>):
    "memref.store"(%v, %m) <{nontemporal = true}> : (i128, memref<i128>) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
