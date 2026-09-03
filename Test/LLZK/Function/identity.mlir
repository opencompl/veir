// RUN: VEIR_ROUNDTRIP
// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"() <{"function_type" = () -> (), "sym_name" = "empty"}> ({
  "function.def"() <{sym_name = "empty", function_type = () -> ()}> ({
    // CHECK:           "function.return"() : () -> ()
    "function.return"() : () -> ()
  // CHECK:         }) : () -> ()
  }) : () -> ()
  // CHECK:         "function.def"() <{"arg_attrs" = [{}], "function_type" = (!felt.type) -> !felt.type, "res_attrs" = [{}], "sym_name" = "passthrough"}> ({
  "function.def"() <{sym_name = "passthrough", function_type = (!felt.type) -> (!felt.type), arg_attrs = [{}], res_attrs = [{}]}> ({
  // CHECK:         ^{{.*}}(%{{.*}}: !felt.type):
  ^entry(%x: !felt.type):
    // CHECK:           "function.return"(%{{.*}}) : (!felt.type) -> ()
    "function.return"(%x) : (!felt.type) -> ()
  // CHECK:         }) : () -> ()
  }) : () -> ()
  // CHECK:         "function.def"() <{"function_type" = () -> (), "sym_name" = "caller"}> ({
  "function.def"() <{sym_name = "caller", function_type = () -> ()}> ({
    // CHECK:           "function.call"() <{"callee" = @empty, "mapOpGroupSizes" = array<i32>, "operandSegmentSizes" = array<i32: 0, 0>}> : () -> ()
    "function.call"() <{callee = @empty, mapOpGroupSizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
    // CHECK:           "function.return"() : () -> ()
    "function.return"() : () -> ()
  // CHECK:         }) : () -> ()
  }) : () -> ()
// CHECK:       }) : () -> ()
}) : () -> ()
