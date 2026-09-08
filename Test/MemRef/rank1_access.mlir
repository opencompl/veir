// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// memref.load and memref.store on a rank-1 memref, each with one `index`
// operand -- the register-file read and write in t2-generic.mlir's `X` and
// `X_write`.  Operand order differs between the two: the load takes the memref
// then the indices, the store takes the value, then the memref, then the
// indices.
//
// Each index must satisfy 0 <= idx < 32.  Nothing checks that; violating it is
// undefined behavior, and MLIR's -generate-runtime-verification pass is what
// inserts the check.  The ASL frontend produces the indices with `index.casts`
// from an i64; VeIR has no `index` dialect, so they arrive as block arguments
// here.
//
// One get_global feeds both accesses: the op is pure and always yields the
// same memref, so re-fetching it per use would be equivalent.

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
