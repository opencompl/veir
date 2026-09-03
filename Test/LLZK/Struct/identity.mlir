// RUN: VEIR_ROUNDTRIP

// CHECK:      "builtin.module"() ({
"builtin.module"() ({
  // CHECK-NEXT: ^{{.*}}():
  // CHECK-NEXT: "struct.def"() <{"sym_name" = "Add"}> ({
  "struct.def"() <{sym_name = "Add"}> ({
    // CHECK-NEXT: ^{{.*}}():
    // CHECK-NEXT: "struct.member"() <{"sym_name" = "x", "type" = !felt.type}> {llzk.pub} : () -> ()
    "struct.member"() <{sym_name = "x", type = !felt.type}> {llzk.pub} : () -> ()
    // CHECK-NEXT: "struct.member"() <{"sym_name" = "y", "type" = !felt.type}> : () -> ()
    "struct.member"() <{sym_name = "y", type = !felt.type}> : () -> ()
    // CHECK-NEXT: "struct.member"() <{"sym_name" = "flag", "type" = i1}> : () -> ()
    "struct.member"() <{sym_name = "flag", type = i1}> : () -> ()
    // CHECK-NEXT: "struct.member"() <{"sym_name" = "position", "type" = index}> : () -> ()
    "struct.member"() <{sym_name = "position", type = index}> : () -> ()
    // CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type) -> !struct.type<@Add>, "sym_name" = "compute"}> ({
    "function.def"() <{function_type = (!felt.type) -> !struct.type<@Add>, sym_name = "compute"}> ({
    // CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type):
    ^bb0(%arg0: !felt.type):
      // CHECK-NEXT: %{{.*}} = "struct.new"() : () -> !struct.type<@Add>
      %self = "struct.new"() : () -> !struct.type<@Add>
      // CHECK-NEXT: "struct.writem"(%{{.*}}, %{{.*}}) <{"member_name" = @x}> : (!struct.type<@Add>, !felt.type) -> ()
      "struct.writem"(%self, %arg0) <{member_name = @x}> : (!struct.type<@Add>, !felt.type) -> ()
      // CHECK-NEXT: "function.return"(%{{.*}}) : (!struct.type<@Add>) -> ()
      "function.return"(%self) : (!struct.type<@Add>) -> ()
    // CHECK-NEXT: }) {function.allow_witness} : () -> ()
    }) {function.allow_witness} : () -> ()
    // CHECK-NEXT: "function.def"() <{"function_type" = (!struct.type<@Add>, !felt.type) -> (), "sym_name" = "constrain"}> ({
    "function.def"() <{function_type = (!struct.type<@Add>, !felt.type) -> (), sym_name = "constrain"}> ({
    // CHECK-NEXT: ^{{.*}}(%{{.*}} : !struct.type<@Add>, %{{.*}} : !felt.type):
    ^bb0(%arg0: !struct.type<@Add>, %arg1: !felt.type):
      // CHECK-NEXT: %{{.*}} = "struct.readm"(%{{.*}}) <{"mapOpGroupSizes" = array<i32>, "member_name" = @x, "numDimsPerMap" = array<i32>}> : (!struct.type<@Add>) -> !felt.type
      %0 = "struct.readm"(%arg0) <{mapOpGroupSizes = array<i32>, member_name = @x, numDimsPerMap = array<i32>}> : (!struct.type<@Add>) -> !felt.type
      // CHECK-NEXT: "constrain.eq"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> ()
      "constrain.eq"(%0, %arg1) : (!felt.type, !felt.type) -> ()
      // CHECK-NEXT: "function.return"() : () -> ()
      "function.return"() : () -> ()
    // CHECK-NEXT: }) {function.allow_constraint} : () -> ()
    }) {function.allow_constraint} : () -> ()
  // CHECK-NEXT: }) : () -> ()
  }) : () -> ()
  // CHECK-NEXT: "struct.def"() <{"sym_name" = "New"}> ({
  "struct.def"() <{sym_name = "New"}> ({
    // CHECK-NEXT: ^{{.*}}():
    // CHECK-NEXT: "struct.member"() <{signal, "sym_name" = "m", "type" = !felt.type}> : () -> ()
    "struct.member"() <{signal, sym_name = "m", type = !felt.type}> : () -> ()
    // CHECK-NEXT: "struct.member"() <{column, "sym_name" = "c", "type" = !felt.type}> : () -> ()
    "struct.member"() <{column, sym_name = "c", type = !felt.type}> : () -> ()
    // CHECK-NEXT: "function.def"() <{"function_type" = (!felt.type) -> !struct.type<@New>, "sym_name" = "compute"}> ({
    "function.def"() <{function_type = (!felt.type) -> !struct.type<@New>, sym_name = "compute"}> ({
    // CHECK-NEXT: ^{{.*}}(%{{.*}} : !felt.type):
    ^bb0(%arg0: !felt.type):
      // CHECK-NEXT: %{{.*}} = "struct.new"() : () -> !struct.type<@New>
      %self = "struct.new"() : () -> !struct.type<@New>
      // CHECK-NEXT: "function.return"(%{{.*}}) : (!struct.type<@New>) -> ()
      "function.return"(%self) : (!struct.type<@New>) -> ()
    // CHECK-NEXT: }) {function.allow_witness} : () -> ()
    }) {function.allow_witness} : () -> ()
    // CHECK-NEXT: "function.def"() <{"function_type" = (!struct.type<@New>, !felt.type) -> (), "sym_name" = "constrain"}> ({
    "function.def"() <{function_type = (!struct.type<@New>, !felt.type) -> (), sym_name = "constrain"}> ({
    // CHECK-NEXT: ^{{.*}}(%{{.*}} : !struct.type<@New>, %{{.*}} : !felt.type):
    ^bb0(%arg0: !struct.type<@New>, %arg1: !felt.type):
      // CHECK-NEXT: %{{.*}} = "struct.readm"(%{{.*}}) <{"mapOpGroupSizes" = array<i32>, "member_name" = @m, "numDimsPerMap" = array<i32>}> : (!struct.type<@New>) -> !felt.type
      %0 = "struct.readm"(%arg0) <{mapOpGroupSizes = array<i32>, member_name = @m, numDimsPerMap = array<i32>}> : (!struct.type<@New>) -> !felt.type
      // CHECK-NEXT: "constrain.eq"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> ()
      "constrain.eq"(%0, %arg1) : (!felt.type, !felt.type) -> ()
      // CHECK-NEXT: "function.return"() : () -> ()
      "function.return"() : () -> ()
    // CHECK-NEXT: }) {function.allow_constraint} : () -> ()
    }) {function.allow_constraint} : () -> ()
  // CHECK-NEXT: }) : () -> ()
  }) : () -> ()
// CHECK-NEXT: }) {llzk.lang} : () -> ()
}) {llzk.lang} : () -> ()
