// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK-NEXT:    ^{{.*}}():
  // CHECK-NEXT:      "include.from"() <{"path" = "lib_a.llzk", "sym_name" = "lib_a"}> : () -> ()
  "include.from"() <{sym_name = "lib_a", path = "lib_a.llzk"}> : () -> ()
  // CHECK-NEXT:      "include.from"() <{"path" = "lib_b.llzk", "sym_name" = "lib_b"}> : () -> ()
  "include.from"() <{sym_name = "lib_b", path = "lib_b.llzk"}> : () -> ()
// CHECK-NEXT: }) : () -> ()
}) : () -> ()
