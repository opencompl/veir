// Demonstrates the declarative-assembly-format (pretty) syntax for the func
// dialect. The input is written in custom syntax; we check that it both
// round-trips as pretty syntax (parse pretty, print pretty) and lowers losslessly
// to the generic form (parse pretty, print generic).

// RUN: veir-opt --pretty %s | filecheck %s --check-prefix=PRETTY
// RUN: veir-opt %s | filecheck %s --check-prefix=GENERIC

"builtin.module"() ({
  func.func @callee(%arg0: i32) -> i32 {
    func.return %arg0 : i32
  }
  func.func @caller(%arg0: i32) -> i32 {
    %0 = func.call @callee(%arg0) : (i32) -> i32
    func.return %0 : i32
  }
}) : () -> ()

// PRETTY:      func.func @callee(%arg{{[0-9]+_[0-9]+}}: i32) -> i32 {
// PRETTY-NEXT:   func.return %arg{{[0-9]+_[0-9]+}} : i32
// PRETTY:      func.func @caller(%arg{{[0-9]+_[0-9]+}}: i32) -> i32 {
// PRETTY:        %{{[0-9]+}} = func.call @callee(%arg{{[0-9]+_[0-9]+}}) : (i32) -> i32
// PRETTY-NEXT:   func.return %{{[0-9]+}} : i32

// GENERIC:      "func.func"() <{"function_type" = (i32) -> i32, "sym_name" = "callee"}> ({
// GENERIC:        "func.return"(%arg{{[0-9]+_[0-9]+}}) : (i32) -> ()
// GENERIC:      "func.call"(%arg{{[0-9]+_[0-9]+}}) <{"callee" = @callee}> : (i32) -> i32
