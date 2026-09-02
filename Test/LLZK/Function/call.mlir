// RUN: VEIR_ROUNDTRIP

// CHECK:      "builtin.module"() ({
"builtin.module"() ({
  // CHECK-NEXT: ^{{.*}}():
  // CHECK-NEXT: "struct.def"() <{"sym_name" = "Sub"}> ({
  "struct.def"() <{sym_name = "Sub"}> ({
    // CHECK-NEXT: ^{{.*}}():
    // CHECK-NEXT: "struct.member"() <{"sym_name" = "x", "type" = !felt.type}> : () -> ()
    "struct.member"() <{sym_name = "x", type = !felt.type}> : () -> ()
    // CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type) -> !struct.type<@Sub>, "sym_name" = "compute"}> ({
    "function.def"() <{function_type = (!felt.type) -> !struct.type<@Sub>, sym_name = "compute"}> ({
    // CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type):
    ^bb0(%arg0: !felt.type):
      // CHECK-NEXT: %{{.*}} = "struct.new"() : () -> !struct.type<@Sub>
      %self = "struct.new"() : () -> !struct.type<@Sub>
      // CHECK-NEXT: "function.return"(%{{.*}}) : (!struct.type<@Sub>) -> ()
      "function.return"(%self) : (!struct.type<@Sub>) -> ()
    // CHECK-NEXT: }) {function.allow_witness} : () -> ()
    }) {function.allow_witness} : () -> ()
    // CHECK-NEXT: "function.def"() <{"function_type" = (!struct.type<@Sub>, !felt.type) -> (), "sym_name" = "constrain"}> ({
    "function.def"() <{function_type = (!struct.type<@Sub>, !felt.type) -> (), sym_name = "constrain"}> ({
    // CHECK-NEXT: ^{{.*}}(%{{.*}} : !struct.type<@Sub>, %{{.*}} : !felt.type):
    ^bb0(%arg0: !struct.type<@Sub>, %arg1: !felt.type):
      // CHECK-NEXT: "function.return"() : () -> ()
      "function.return"() : () -> ()
    // CHECK-NEXT: }) {function.allow_constraint} : () -> ()
    }) {function.allow_constraint} : () -> ()
  // CHECK-NEXT: }) : () -> ()
  }) : () -> ()
  // CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type) -> (), "sym_name" = "main"}> ({
  "function.def"() <{function_type = (!felt.type) -> (), sym_name = "main"}> ({
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type):
  ^bb0(%arg0: !felt.type):
    // CHECK-NEXT: %{{.*}} = "function.call"(%{{.*}}) <{"callee" = @Sub::@compute, "mapOpGroupSizes" = array<i32>, "numDimsPerMap" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0>}> : (!felt.type) -> !struct.type<@Sub>
    %s = "function.call"(%arg0) <{callee = @Sub::@compute, mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!felt.type) -> !struct.type<@Sub>
    // CHECK-NEXT: "function.call"(%{{.*}}, %{{.*}}) <{"callee" = @Sub::@constrain, "mapOpGroupSizes" = array<i32>, "numDimsPerMap" = array<i32>, "operandSegmentSizes" = array<i32: 2, 0>}> : (!struct.type<@Sub>, !felt.type) -> ()
    "function.call"(%s, %arg0) <{callee = @Sub::@constrain, mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!struct.type<@Sub>, !felt.type) -> ()
    // CHECK-NEXT: "function.return"() : () -> ()
    "function.return"() : () -> ()
  // CHECK-NEXT: }) {function.allow_constraint, function.allow_witness} : () -> ()
  }) {function.allow_constraint, function.allow_witness} : () -> ()
// CHECK-NEXT: }) {llzk.lang} : () -> ()
}) {llzk.lang} : () -> ()
