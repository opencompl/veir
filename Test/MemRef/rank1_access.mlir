// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// memref.load and memref.store on a rank-1 memref, each with one `index`
// operand -- the register-file read and write in t2-generic.mlir's `X` and
// `X_write`.

"builtin.module"() ({
  "memref.global"() <{sym_name = "_X", type = memref<32xi128>}> : () -> ()
  "func.func"() <{function_type = (index, index) -> (), sym_name = "copy_reg"}> ({
  ^bb0(%arg0: index, %arg1: index):
    %0 = "memref.get_global"() <{name = @_X}> : () -> memref<32xi128>
    %1 = "memref.load"(%0, %arg0) : (memref<32xi128>, index) -> i128
    "memref.store"(%1, %0, %arg1) : (i128, memref<32xi128>, index) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"()
// CHECK-SAME:   "sym_name" = "copy_reg"
// CHECK:      ^{{.*}}(%[[SRC:[^ ]+]] : index, %[[DST:[^ ]+]] : index):
// CHECK:      %[[X:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @_X
// CHECK-SAME:   : () -> memref<32xi128>
// CHECK:      %[[V:.*]] = "memref.load"(%[[X]], %[[SRC]]) : (memref<32xi128>, index) -> i128
// CHECK:      "memref.store"(%[[V]], %[[X]], %[[DST]]) : (i128, memref<32xi128>, index) -> ()
// CHECK:      "func.return"() : () -> ()
