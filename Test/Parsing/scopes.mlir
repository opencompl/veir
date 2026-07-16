// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "outer", function_type = () -> ()}> ({
  ^bb0:
      %a = "test.test"() : () -> i1
  
      "test.test"() ({
          "test.test"(%a) : (i1) -> ()
          %b = "test.test"() : () -> i2
  
          "func.func"() <{sym_name = "inner_i3", function_type = () -> ()}> ({
          ^bb0:
              %c = "test.test"() : () -> i3
              "cf.br"() [^bb1] : () -> ()
          ^bb1:
              "test.test"(%a, %b, %c) : (i1, i2, i3) -> ()
              "func.return"() : () -> ()
          }) : () -> ()
  
          "func.func"() <{sym_name = "inner_i4", function_type = () -> ()}> ({
          ^bb0:
              %c = "test.test"() : () -> i4
              "cf.br"() [^bb1] : () -> ()
          ^bb1:
              "test.test"(%a, %b, %c) : (i1, i2, i4) -> ()
              "func.return"() : () -> ()
          }) : () -> ()
  
          %c = "test.test"() : () -> i5
          "test.test"(%a, %b, %c) : (i1, i2, i5) -> ()
      }) : () -> ()

      "cf.br"() [^bb1] : () -> ()
  ^bb1:
      %b, %c = "test.test"() : () -> (i6, i7)
      "test.test"(%a, %b, %c) : (i1, i6, i7) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{{.*}}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %[[A:.*]] = "test.test"() : () -> i1
// CHECK-NEXT:         "test.test"() ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             "test.test"(%[[A]]) : (i1) -> ()
// CHECK-NEXT:             %[[B:.*]] = "test.test"() : () -> i2
// CHECK-NEXT:             "func.func"() <{{.*}}> ({
// CHECK-NEXT:               ^{{.*}}():
// CHECK-NEXT:                 %[[C3:.*]] = "test.test"() : () -> i3
// CHECK-NEXT:                 "cf.br"() [^[[C3_USE:.*]]] : () -> ()
// CHECK-NEXT:               ^[[C3_USE]]():
// CHECK-NEXT:                 "test.test"(%[[A]], %[[B]], %[[C3]]) : (i1, i2, i3) -> ()
// CHECK-NEXT:                 "func.return"() : () -> ()
// CHECK-NEXT:             }) : () -> ()
// CHECK-NEXT:             "func.func"() <{{.*}}> ({
// CHECK-NEXT:               ^{{.*}}():
// CHECK-NEXT:                 %[[C4:.*]] = "test.test"() : () -> i4
// CHECK-NEXT:                 "cf.br"() [^[[C4_USE:.*]]] : () -> ()
// CHECK-NEXT:               ^[[C4_USE]]():
// CHECK-NEXT:                 "test.test"(%[[A]], %[[B]], %[[C4]]) : (i1, i2, i4) -> ()
// CHECK-NEXT:                 "func.return"() : () -> ()
// CHECK-NEXT:             }) : () -> ()
// CHECK-NEXT:             %[[C5:.*]] = "test.test"() : () -> i5
// CHECK-NEXT:             "test.test"(%[[A]], %[[B]], %[[C5]]) : (i1, i2, i5) -> ()
// CHECK-NEXT:         }) : () -> ()
// CHECK-NEXT:         "cf.br"() [^[[OUTER_USE:.*]]] : () -> ()
// CHECK-NEXT:       ^[[OUTER_USE]]():
// CHECK-NEXT:         %[[B6C7:.*]]:2 = "test.test"() : () -> (i6, i7)
// CHECK-NEXT:         "test.test"(%[[A]], %[[B6C7]]#0, %[[B6C7]]#1) : (i1, i6, i7) -> ()
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
