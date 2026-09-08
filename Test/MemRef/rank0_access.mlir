// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "memref.global"() <{sym_name = "Halted", type = memref<i1>}> : () -> ()
  "memref.global"() <{sym_name = "_PC", type = memref<i128>}> : () -> ()
  "func.func"() <{function_type = (i128) -> i1, sym_name = "write_pc_and_read_halted"}> ({
  ^bb0(%arg0: i128):
    %0 = "memref.get_global"() <{name = @_PC}> : () -> memref<i128>
    "memref.store"(%arg0, %0) : (i128, memref<i128>) -> ()
    %1 = "memref.get_global"() <{name = @Halted}> : () -> memref<i1>
    %2 = "memref.load"(%1) : (memref<i1>) -> i1
    "func.return"(%2) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"()
// CHECK-SAME:   "sym_name" = "write_pc_and_read_halted"
// CHECK:      ^{{.*}}(%[[PCVAL:[^ ]+]] : i128):
// CHECK:      %[[PC:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @_PC
// CHECK-SAME:   : () -> memref<i128>
// CHECK:      "memref.store"(%[[PCVAL]], %[[PC]]) : (i128, memref<i128>) -> ()
// CHECK:      %[[H:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @Halted
// CHECK-SAME:   : () -> memref<i1>
// CHECK:      %[[V:.*]] = "memref.load"(%[[H]]) : (memref<i1>) -> i1
// CHECK:      "func.return"(%[[V]]) : (i1) -> ()
