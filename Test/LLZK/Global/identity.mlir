// RUN: VEIR_ROUNDTRIP
//
// Note: sym_name is StringAttr (LLZK's SymbolNameAttr → "name"), not
// FlatSymbolRefAttr (`@name`). The `@` form is only for SymbolRefAttr
// users like global.read/global.write's name_ref.

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK-NEXT:    ^{{.*}}():
  // CHECK-NEXT:      "global.def"() <{constant, "initial_value" = #felt<const 0>, "sym_name" = "counter", "type" = !felt.type}> : () -> ()
  "global.def"() <{sym_name = "counter", constant, type = !felt.type, initial_value = #felt<const 0> : !felt.type}> : () -> ()
  // CHECK-NEXT:      "global.def"() <{constant, "initial_value" = #felt<const 42>, "sym_name" = "initial", "type" = !felt.type}> : () -> ()
  "global.def"() <{sym_name = "initial", constant, type = !felt.type, initial_value = #felt<const 42> : !felt.type}> : () -> ()
  // CHECK-NEXT:      "global.def"() <{"sym_name" = "mutable", "type" = !felt.type}> : () -> ()
  "global.def"() <{sym_name = "mutable", type = !felt.type}> : () -> ()
  // CHECK-NEXT:      "function.def"() <{"function_type" = () -> (), "sym_name" = "global_identity"}> ({
  "function.def"() <{sym_name = "global_identity", function_type = () -> ()}> ({
    // CHECK:           %{{.*}} = "global.read"() <{"name_ref" = @counter}> : () -> !felt.type
    %v = "global.read"() <{name_ref = @counter}> : () -> !felt.type
    // CHECK-NEXT:      "global.write"(%{{.*}}) <{"name_ref" = @mutable}> : (!felt.type) -> ()
    "global.write"(%v) <{name_ref = @mutable}> : (!felt.type) -> ()
    // CHECK-NEXT:      "function.return"() : () -> ()
    "function.return"() : () -> ()
  }) {function.allow_witness} : () -> ()
}) {llzk.lang} : () -> ()
