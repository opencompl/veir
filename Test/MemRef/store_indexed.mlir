// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// memref.store to a rank-1 memref with one `index` operand -- the register-file
// write in t2-generic.mlir's `X_write`.  Operand order is value, memref,
// indices.  The in-bounds requirement 0 <= idx < 32 is a precondition memref
// assumes rather than checks; MLIR's -generate-runtime-verification pass can
// insert the check.

"builtin.module"() ({
  "memref.global"() <{sym_name = "_X", type = memref<32xi128>}> : () -> ()
  "func.func"() <{function_type = (index, i128) -> (), sym_name = "write_reg"}> ({
  ^bb0(%arg0: index, %arg1: i128):
    %0 = "memref.get_global"() <{name = @_X}> : () -> memref<32xi128>
    "memref.store"(%arg1, %0, %arg0) : (i128, memref<32xi128>, index) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"()
// CHECK-SAME:   "sym_name" = "write_reg"
// CHECK:      ^{{.*}}(%[[I:[^ ]+]] : index, %[[V:[^ ]+]] : i128):
// CHECK:      %[[G:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @_X
// CHECK:      "memref.store"(%[[V]], %[[G]], %[[I]]) : (i128, memref<32xi128>, index) -> ()
