// RUN: veir-opt %s | filecheck %s
//
// Function dialect prototype (Phase F.5). Tests function.def with a
// body region containing function.return as terminator.
//
// `function_type` is required by LLZK (TypeAttrOf<FunctionType>) and
// by VEIR's FunctionDefProperties. It mirrors the op's generic-form
// type signature.

"builtin.module"() ({
  "function.def"() <{sym_name = "empty", function_type = () -> ()}> ({
    "function.return"() : () -> ()
  }) : () -> ()
  "function.def"() <{sym_name = "passthrough", function_type = (!felt.type) -> ()}> ({
  ^entry(%x: !felt.type):
    "function.return"(%x) : (!felt.type) -> ()
  }) : () -> ()
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK:         "function.def"() <{"function_type" = () -> (), "sym_name" = "empty"}> ({
// CHECK:           "function.return"() : () -> ()
// CHECK:         }) : () -> ()
// CHECK:         "function.def"() <{"function_type" = (!felt.type) -> (), "sym_name" = "passthrough"}> ({
// CHECK:         ^{{.*}}(%{{.*}}: !felt.type):
// CHECK:           "function.return"(%{{.*}}) : (!felt.type) -> ()
// CHECK:         }) : () -> ()
// CHECK:       }) : () -> ()
