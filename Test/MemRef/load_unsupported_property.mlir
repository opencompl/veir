// RUN: not veir-opt %s 2>&1 | filecheck %s

// MLIR gives memref.load optional `nontemporal`, `alignment`, and `invariant`
// attributes.  To avoid silently dropping these, we simply error out on them
// until we support them.

"builtin.module"() ({
  "func.func"() <{function_type = (memref<i128>) -> i128, sym_name = "f"}> ({
  ^bb0(%m: memref<i128>):
    %0 = "memref.load"(%m) <{alignment = 16 : i64, nontemporal = true}> : (memref<i128>) -> i128
    "func.return"(%0) : (i128) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: memref.load: expected no properties, but got 2 properties: alignment, nontemporal
