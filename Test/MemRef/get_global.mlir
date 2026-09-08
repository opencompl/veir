// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "memref.global"() <{sym_name = "_PC", type = memref<i128>}> : () -> ()
  "memref.global"() <{sym_name = "_X", type = memref<32xi128>}> : () -> ()
  "func.func"() <{function_type = () -> (memref<i128>, memref<32xi128>), sym_name = "get_pc_and_regs"}> ({
    %0 = "memref.get_global"() <{name = @_PC}> : () -> memref<i128>
    %1 = "memref.get_global"() <{name = @_X}> : () -> memref<32xi128>
    "func.return"(%0, %1) : (memref<i128>, memref<32xi128>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"()
// CHECK-SAME:   "sym_name" = "get_pc_and_regs"
// CHECK:      %[[PC:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @_PC
// CHECK-SAME:   : () -> memref<i128>
// CHECK:      %[[X:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @_X
// CHECK-SAME:   : () -> memref<32xi128>
// CHECK:      "func.return"(%[[PC]], %[[X]]) : (memref<i128>, memref<32xi128>) -> ()
