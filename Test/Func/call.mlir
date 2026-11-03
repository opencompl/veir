// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "callee"}> ({
  ^bb0(%arg0: i32):
    "func.return"(%arg0) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{function_type = (i32) -> i32, sym_name = "caller"}> ({
  ^bb0(%arg0: i32):
    %0 = "func.call"(%arg0) <{callee = @callee}> : (i32) -> i32
    "func.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.call"(%arg{{[0-9]+_[0-9]+}}) <{
// CHECK-SAME:   "callee" = @callee
// CHECK-SAME: }> : (i32) -> i32
