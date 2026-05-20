// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "include.from"() <{sym_name = "lib_a", path = "lib_a.llzk"}> : () -> ()
  "include.from"() <{sym_name = "lib_b", path = "lib_b.llzk"}> : () -> ()
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
// CHECK-NEXT:      "include.from"() <{"path" = "lib_a.llzk", "sym_name" = "lib_a"}> : () -> ()
// CHECK-NEXT:      "include.from"() <{"path" = "lib_b.llzk", "sym_name" = "lib_b"}> : () -> ()
// CHECK-NEXT: }) : () -> ()
