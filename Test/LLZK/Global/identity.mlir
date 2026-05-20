// RUN: VEIR_ROUNDTRIP
//
// Note: sym_name is StringAttr (LLZK's SymbolNameAttr → "name"), not
// FlatSymbolRefAttr (`@name`). The `@` form is only for SymbolRefAttr
// users like global.read/global.write's name_ref.

"builtin.module"() ({
  "global.def"() <{sym_name = "counter", constant, type = i32}> : () -> ()
  "global.def"() <{sym_name = "initial", constant, type = i32, initial_value = 42 : i32}> : () -> ()
  "global.def"() <{sym_name = "mutable", type = i32}> : () -> ()
  %v = "global.read"() <{name_ref = @counter}> : () -> i32
  "global.write"(%v) <{name_ref = @mutable}> : (i32) -> ()
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
// CHECK-NEXT:      "global.def"() <{constant, "sym_name" = "counter", "type" = i32}> : () -> ()
// CHECK-NEXT:      "global.def"() <{constant, "initial_value" = 42 : i32, "sym_name" = "initial", "type" = i32}> : () -> ()
// CHECK-NEXT:      "global.def"() <{"sym_name" = "mutable", "type" = i32}> : () -> ()
// CHECK-NEXT:      %{{.*}} = "global.read"() <{"name_ref" = @counter}> : () -> i32
// CHECK-NEXT:      "global.write"(%{{.*}}) <{"name_ref" = @mutable}> : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
