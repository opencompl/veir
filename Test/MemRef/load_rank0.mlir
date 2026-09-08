// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// memref.load from a rank-0 memref.  The number of indices must equal the rank,
// so a rank-0 load takes the memref and nothing else.  This is how
// t2-generic.mlir reads its scalar state cells (`Halted`, `_NextPC`).

"builtin.module"() ({
  "memref.global"() <{sym_name = "Halted", type = memref<i1>}> : () -> ()
  "func.func"() <{function_type = () -> i1, sym_name = "read_halted"}> ({
    %0 = "memref.get_global"() <{name = @Halted}> : () -> memref<i1>
    %1 = "memref.load"(%0) : (memref<i1>) -> i1
    "func.return"(%1) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"()
// CHECK-SAME:   "sym_name" = "read_halted"
// CHECK:      %[[G:.*]] = "memref.get_global"()
// CHECK-SAME:   "name" = @Halted
// CHECK:      %[[V:.*]] = "memref.load"(%[[G]]) : (memref<i1>) -> i1
// CHECK:      "func.return"(%[[V]]) : (i1) -> ()
