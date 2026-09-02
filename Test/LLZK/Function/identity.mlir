// RUN: VEIR_ROUNDTRIP
// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"() <{"function_type" = () -> (), "sym_name" = "empty"}> ({
  "function.def"() <{sym_name = "empty", function_type = () -> ()}> ({
    // CHECK:           "function.return"() : () -> ()
    "function.return"() : () -> ()
  // CHECK:         }) : () -> ()
  }) : () -> ()
  // CHECK:         "function.def"() <{"function_type" = (!felt.type) -> !felt.type, "sym_name" = "passthrough"}> ({
  "function.def"() <{sym_name = "passthrough", function_type = (!felt.type) -> (!felt.type)}> ({
  // CHECK:         ^{{.*}}(%{{.*}}: !felt.type):
  ^entry(%x: !felt.type):
    // CHECK:           "function.return"(%{{.*}}) : (!felt.type) -> ()
    "function.return"(%x) : (!felt.type) -> ()
  // CHECK:         }) : () -> ()
  }) : () -> ()
// CHECK:       }) : () -> ()
}) : () -> ()
