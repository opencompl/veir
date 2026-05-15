// RUN: veir-opt %s | filecheck %s

"test.test"() ({
    %a = "test.test"() : () -> i1

    "test.test"() ({
        "test.test"(%a) : (i1) -> ()
        %b = "test.test"() : () -> i2

        "test.test"() ({
        ^bb0:
            %c = "test.test"() : () -> i3
        ^bb1:
            "test.test"(%a, %b, %c) : (i1, i2, i3) -> ()
        }) : () -> ()

        "test.test"() ({
        ^bb0:
            %c = "test.test"() : () -> i4
        ^bb1:
            "test.test"(%a, %b, %c) : (i1, i2, i4) -> ()
        }) : () -> ()

        %c = "test.test"() : () -> i5
        "test.test"(%a, %b, %c) : (i1, i2, i5) -> ()
    }) : () -> ()

^bb1:
    %b, %c = "test.test"() : () -> (i6, i7)
    "test.test"(%a, %b, %c) : (i1, i6, i7) -> ()
}) : () -> ()

// CHECK:      "test.test"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %[[A:.*]] = "test.test"() : () -> i1
// CHECK-NEXT:     "test.test"() ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         "test.test"(%[[A]]) : (i1) -> ()
// CHECK-NEXT:         %[[B:.*]] = "test.test"() : () -> i2
// CHECK-NEXT:         "test.test"() ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             %[[C3:.*]] = "test.test"() : () -> i3
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             "test.test"(%[[A]], %[[B]], %[[C3]]) : (i1, i2, i3) -> ()
// CHECK-NEXT:         }) : () -> ()
// CHECK-NEXT:         "test.test"() ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             %[[C4:.*]] = "test.test"() : () -> i4
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             "test.test"(%[[A]], %[[B]], %[[C4]]) : (i1, i2, i4) -> ()
// CHECK-NEXT:         }) : () -> ()
// CHECK-NEXT:         %[[C5:.*]] = "test.test"() : () -> i5
// CHECK-NEXT:         "test.test"(%[[A]], %[[B]], %[[C5]]) : (i1, i2, i5) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %[[B6:.*]], %[[C7:.*]] = "test.test"() : () -> (i6, i7)
// CHECK-NEXT:     "test.test"(%[[A]], %[[B6]], %[[C7]]) : (i1, i6, i7) -> ()
// CHECK-NEXT: }) : () -> ()
