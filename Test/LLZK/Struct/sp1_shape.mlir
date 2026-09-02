// RUN: VEIR_ROUNDTRIP

// CHECK:      "builtin.module"() ({
"builtin.module"() ({
  // CHECK-NEXT: ^{{.*}}():
  // CHECK-NEXT: "struct.def"() <{"sym_name" = "Add"}> ({
  "struct.def"() <{sym_name = "Add"}> ({
    // CHECK-NEXT: ^{{.*}}():
    // CHECK-NEXT: "struct.member"() <{"sym_name" = "add_operation_29", "type" = !felt.type}> {llzk.pub} : () -> ()
    "struct.member"() <{sym_name = "add_operation_29", type = !felt.type}> {llzk.pub} : () -> ()
    // CHECK-NEXT: "struct.member"() <{"sym_name" = "is_real_33", "type" = !felt.type}> : () -> ()
    "struct.member"() <{sym_name = "is_real_33", type = !felt.type}> : () -> ()
    // CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type, !felt.type) -> !struct.type<@Add>, "sym_name" = "compute"}> ({
    "function.def"() <{function_type = (!felt.type, !felt.type) -> !struct.type<@Add>, sym_name = "compute"}> ({
    // CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type, %{{.*}} : !felt.type):
    ^bb0(%arg0: !felt.type, %arg1: !felt.type):
      // CHECK-NEXT: %{{.*}} = "struct.new"() : () -> !struct.type<@Add>
      %0 = "struct.new"() : () -> !struct.type<@Add>
      // CHECK-NEXT: "function.return"(%{{.*}}) : (!struct.type<@Add>) -> ()
      "function.return"(%0) : (!struct.type<@Add>) -> ()
    // CHECK-NEXT: }) {function.allow_witness} : () -> ()
    }) {function.allow_witness} : () -> ()
    // CHECK-NEXT: "function.def"() <{"function_type" = (!struct.type<@Add>, !felt.type, !felt.type) -> (), "sym_name" = "constrain"}> ({
    "function.def"() <{function_type = (!struct.type<@Add>, !felt.type, !felt.type) -> (), sym_name = "constrain"}> ({
    // CHECK-NEXT: ^{{.*}}(%{{.*}} : !struct.type<@Add>, %{{.*}} : !felt.type, %{{.*}} : !felt.type):
    ^bb0(%arg0: !struct.type<@Add>, %arg1: !felt.type, %arg2: !felt.type):
      // CHECK-NEXT: %{{.*}} = "felt.const"() <{"value" = #felt<const 2130673921>}> : () -> !felt.type
      %0 = "felt.const"() <{value = #felt<const 2130673921> : !felt.type}> : () -> !felt.type
      // CHECK-NEXT: %{{.*}} = "struct.readm"(%{{.*}}) <{"mapOpGroupSizes" = array<i32>, "member_name" = @add_operation_29, "numDimsPerMap" = array<i32>}> : (!struct.type<@Add>) -> !felt.type
      %1 = "struct.readm"(%arg0) <{mapOpGroupSizes = array<i32>, member_name = @add_operation_29, numDimsPerMap = array<i32>}> : (!struct.type<@Add>) -> !felt.type
      // CHECK-NEXT: %{{.*}} = "felt.add"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
      %2 = "felt.add"(%arg1, %arg2) : (!felt.type, !felt.type) -> !felt.type
      // CHECK-NEXT: %{{.*}} = "felt.sub"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
      %3 = "felt.sub"(%2, %1) : (!felt.type, !felt.type) -> !felt.type
      // CHECK-NEXT: %{{.*}} = "felt.mul"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
      %4 = "felt.mul"(%3, %0) : (!felt.type, !felt.type) -> !felt.type
      // CHECK-NEXT: "constrain.eq"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> ()
      "constrain.eq"(%4, %1) : (!felt.type, !felt.type) -> ()
      // CHECK-NEXT: "function.return"() : () -> ()
      "function.return"() : () -> ()
    // CHECK-NEXT: }) {function.allow_constraint} : () -> ()
    }) {function.allow_constraint} : () -> ()
  // CHECK-NEXT: }) : () -> ()
  }) : () -> ()
// CHECK-NEXT: }) {llzk.lang} : () -> ()
}) {llzk.lang} : () -> ()
