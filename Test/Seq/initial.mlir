// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// CHECK: "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "hw.module"() <{{.*}}"sym_name" = "top"{{.*}}> ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: %[[INIT:[^ :]+]]:2 = "seq.initial"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: %[[F:[^ ]+]] = "hw.constant"() <{"value" = false}> : () -> i1
// CHECK-NEXT: %[[C:[^ ]+]] = "hw.constant"() <{"value" = 5 : i8}> : () -> i8
// CHECK-NEXT: "seq.yield"(%[[F]], %[[C]]) : (i1, i8) -> ()
// CHECK-NEXT: }) : () -> (!seq.immutable<i1>, !seq.immutable<i8>)
// CHECK-NEXT: %[[NEXT:[^ ]+]] = "seq.initial"(%[[INIT]]#1) ({
// CHECK-NEXT: ^{{.*}}(%[[X:[^ ]+]] : i8):
// CHECK-NEXT: "seq.yield"(%[[X]]) : (i8) -> ()
// CHECK-NEXT: }) : (!seq.immutable<i8>) -> !seq.immutable<i8>
// CHECK-NEXT: "seq.initial"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "seq.yield"() : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: "hw.output"() : () -> ()

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<>, parameters = [], per_port_attrs = [], sym_name = "top"}> ({
    %init:2 = "seq.initial"() ({
      %false = "hw.constant"() <{value = false}> : () -> i1
      %c5 = "hw.constant"() <{value = 5 : i8}> : () -> i8
      "seq.yield"(%false, %c5) : (i1, i8) -> ()
    }) : () -> (!seq.immutable<i1>, !seq.immutable<i8>)
    %next = "seq.initial"(%init#1) ({
    ^bb0(%x: i8):
      "seq.yield"(%x) : (i8) -> ()
    }) : (!seq.immutable<i8>) -> !seq.immutable<i8>
    "seq.initial"() ({
      "seq.yield"() : () -> ()
    }) : () -> ()
    "hw.output"() : () -> ()
  }) : () -> ()
}) : () -> ()
