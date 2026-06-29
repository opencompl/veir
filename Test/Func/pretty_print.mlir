// Custom (pretty) printing of the func dialect via the declarative assembly
// format. The input is in generic form; with --pretty the func ops are printed
// in their custom syntax.

// RUN: veir-opt --pretty %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "callee"}> ({
  ^bb0(%arg0: i32):
    "func.return"(%arg0) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{function_type = (i32) -> i32, sym_name = "caller"}> ({
  ^bb0(%arg0: i32):
    %0 = "func.call"(%arg0) <{callee = @callee}> : (i32) -> i32
    "func.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      func.func @callee(%arg{{[0-9]+_[0-9]+}}: i32) -> i32 {
// CHECK-NEXT:   func.return %arg{{[0-9]+_[0-9]+}} : i32
// CHECK:      func.func @caller(%arg{{[0-9]+_[0-9]+}}: i32) -> i32 {
// CHECK:        %{{[0-9]+}} = func.call @callee(%arg{{[0-9]+_[0-9]+}}) : (i32) -> i32
// CHECK-NEXT:   func.return %{{[0-9]+}} : i32
