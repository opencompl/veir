// RUN: not veir-opt %s 2>&1 | filecheck %s

// Unlike `llvm.call`, `func.call` is never indirect: `FuncCallProperties`
// requires the `callee` symbol, so omitting it must be rejected.
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "caller"}> ({
  ^bb0(%arg0: i32):
    %0 = "func.call"(%arg0) : (i32) -> i32
    "func.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.call: expected a 'callee' symbol reference
