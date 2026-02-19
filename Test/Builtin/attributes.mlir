// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %3 = "test.test"() {str = "hello world"} : () -> i32
  %4 = "test.test"() {empty = ""} : () -> i32
  %5 = "test.test"() {escaped = "line1\nline2\ttab"} : () -> i32
  %6 = "test.test"() {unregistered = #unregistered.dialect<foo 3 + 2>} : () -> i32
  %7 = "test.test"() {u = unit} : () -> i32
  %8 = "test.test"() {u} : () -> i32
  %9 = "test.test"() {dict = {a = 0 : i32, b = "hello"}} : () -> i32
  %10 = "test.test"() {empty_dict = {}} : () -> i32
  %11 = "test.test"() {dict_unit = {x, y}} : () -> i32
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "test.test"() {str = "hello world"} : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() {empty = ""} : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() {escaped = "line1\nline2\ttab"} : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() {unregistered = #unregistered.dialect<foo 3 + 2>} : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() {u} : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() {u} : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() {dict = {a = 0 : i32, b = "hello"}} : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() {empty_dict = {}} : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() {dict_unit = {x, y}} : () -> i32
// CHECK-NEXT: }) : () -> ()
