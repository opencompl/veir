// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// memref.store to a rank-0 memref: value first, then the memref, then rank-many
// indices (none here).  t2-generic.mlir writes `_PC`/`_NextPC`/`Halted` this
// way.  Note the store is legal only because the global is not `constant`;
// storing through a get_global of a constant global is undefined behavior.

"builtin.module"() ({
  "memref.global"() <{sym_name = "_PC", type = memref<i128>}> : () -> ()
  "func.func"() <{function_type = (i128) -> (), sym_name = "write_pc"}> ({
  ^bb0(%arg0: i128):
    %0 = "memref.get_global"() <{name = @_PC}> : () -> memref<i128>
    "memref.store"(%arg0, %0) : (i128, memref<i128>) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"()
// CHECK-SAME:   "sym_name" = "write_pc"
// CHECK:      ^{{.*}}(%[[V:[^ ]+]] : i128):
// CHECK:      %[[G:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @_PC
// CHECK:      "memref.store"(%[[V]], %[[G]]) : (i128, memref<i128>) -> ()
