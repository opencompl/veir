// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "f"}> ({
  ^bb0(%arg0: i32):
    "func.return"(%arg0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      func.func @f(%{{.*}}: i32) -> i32 {
// CHECK:        "func.return"(%{{.*}}) : (i32) -> ()
// CHECK:      }

