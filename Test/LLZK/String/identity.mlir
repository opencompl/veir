// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
^bb0():
  %0 = "string.new"() <{value = "hello"}> : () -> !string.type
  %1 = "string.new"() <{value = "world"}> : () -> !string.type
  %2 = "string.new"() <{value = ""}> : () -> !string.type
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
// CHECK-NEXT:      %{{.*}} = "string.new"() <{"value" = "hello"}> : () -> !string.type
// CHECK-NEXT:      %{{.*}} = "string.new"() <{"value" = "world"}> : () -> !string.type
// CHECK-NEXT:      %{{.*}} = "string.new"() <{"value" = ""}> : () -> !string.type
// CHECK-NEXT: }) : () -> ()
