// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
^bb0():
  // CHECK-NEXT:      %{{.*}} = "string.new"() <{"value" = "hello"}> : () -> !string.type
  %0 = "string.new"() <{value = "hello"}> : () -> !string.type
  // CHECK-NEXT:      %{{.*}} = "string.new"() <{"value" = "world"}> : () -> !string.type
  %1 = "string.new"() <{value = "world"}> : () -> !string.type
  // CHECK-NEXT:      %{{.*}} = "string.new"() <{"value" = ""}> : () -> !string.type
  %2 = "string.new"() <{value = ""}> : () -> !string.type
// CHECK-NEXT: }) : () -> ()
}) : () -> ()
