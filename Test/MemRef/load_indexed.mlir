// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "memref.global"() <{sym_name = "_X", type = memref<32xi128>}> : () -> ()
  "func.func"() <{function_type = (index) -> i128, sym_name = "read_reg"}> ({
  ^bb0(%arg0: index):
    %0 = "memref.get_global"() <{name = @_X}> : () -> memref<32xi128>
    %1 = "memref.load"(%0, %arg0) : (memref<32xi128>, index) -> i128
    "func.return"(%1) : (i128) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"()
// CHECK-SAME:   "sym_name" = "read_reg"
// CHECK:      ^{{.*}}(%[[I:[^ ]+]] : index):
// CHECK:      %[[G:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @_X
// CHECK:      %[[V:.*]] = "memref.load"(%[[G]], %[[I]]) : (memref<32xi128>, index) -> i128
// CHECK:      "func.return"(%[[V]]) : (i128) -> ()
