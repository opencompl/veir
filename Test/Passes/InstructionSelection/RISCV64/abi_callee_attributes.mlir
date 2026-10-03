// RUN: veir-opt %s --print-op-generic -p=isel-abi-riscv64 | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// Calls must honor ABI attributes found only on their callees, including
// declarations after the caller and discardable attributes. Quoted and escaped
// references must resolve to the same symbol as a bare reference.
"builtin.module"() ({
  "func.func"() <{sym_name = "caller", function_type = (!llvm.ptr, i32) -> ()}> ({
  ^bb0(%p: !llvm.ptr, %a: i32):
    "func.call"(%p) <{callee = @byval}> : (!llvm.ptr) -> ()
    "func.call"(%p) <{callee = @"byval"}> : (!llvm.ptr) -> ()
    "func.call"(%p) <{callee = @"byv\61l"}> : (!llvm.ptr) -> ()
    "llvm.call"(%p) <{callee = @nest}> : (!llvm.ptr) -> ()
    %r = "func.call"(%a) <{callee = @result}> : (i32) -> i32
    "llvm.call"() <{callee = @fast}> : () -> ()
    "func.call"(%p) <{callee = @discardable}> : (!llvm.ptr) -> ()
    "func.call"(%p) <{callee = @"nonutf8\FF"}> : (!llvm.ptr) -> ()
    // Supported declarations, unresolved external symbols, and indirect calls
    // remain eligible. An unsupported symbol in a nested module is unrelated.
    "func.call"(%p) <{callee = @ordinary}> : (!llvm.ptr) -> ()
    "llvm.call"() <{callee = @external}> : () -> ()
    "llvm.call"(%p) : (!llvm.ptr) -> ()
    "func.call"(%p) <{callee = @shadow}> : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "caller"
  // CHECK: "func.call"(%{{.*}}) <{"callee" = @byval}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: "func.call"(%{{.*}}) <{"callee" = @"byval"}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: "func.call"(%{{.*}}) <{"callee" = @"byv\61l"}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: "llvm.call"(%{{.*}}) <{"callee" = @nest}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: %{{.*}} = "func.call"(%{{.*}}) <{"callee" = @result}> : (i32) -> i32
  // CHECK-NEXT: "llvm.call"() <{"callee" = @fast}> : () -> ()
  // CHECK-NEXT: "func.call"(%{{.*}}) <{"callee" = @discardable}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: "func.call"(%{{.*}}) <{"callee" = @"nonutf8\FF"}> : (!llvm.ptr) -> ()
  // CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @ordinary}> : (!riscv.reg) -> ()
  // CHECK: "riscv_cf.call"() <{"callee" = @external}> : () -> ()
  // CHECK: "riscv_cf.call"(%{{.*}}) : (!riscv.reg) -> ()
  // CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @shadow}> : (!riscv.reg) -> ()
  // CHECK-NEXT: "riscv_cf.return"() : () -> ()

  "func.func"() <{sym_name = "byval", function_type = (!llvm.ptr) -> (), arg_attrs = [{llvm.byval = i64}], sym_visibility = "private"}> ({}) : () -> ()
  "llvm.func"() <{sym_name = "nest", function_type = !llvm.func<void (ptr)>, arg_attrs = [{llvm.nest}]}> ({}) : () -> ()
  "func.func"() <{sym_name = "result", function_type = (i32) -> i32, res_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%a: i32):
    "func.return"(%a) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "fast", function_type = !llvm.func<void ()>, CConv = #llvm.cconv<fastcc>}> ({}) : () -> ()
  "func.func"() <{sym_name = "discardable", function_type = (!llvm.ptr) -> (), sym_visibility = "private"}> ({}) {arg_attrs = [{llvm.byval = i64}]} : () -> ()
  "func.func"() <{sym_name = "nonutf8\FF", function_type = (!llvm.ptr) -> (), arg_attrs = [{llvm.byval = i64}], sym_visibility = "private"}> ({}) : () -> ()
  "func.func"() <{sym_name = "ordinary", function_type = (!llvm.ptr) -> (), arg_attrs = [{llvm.noundef}], sym_visibility = "private"}> ({}) : () -> ()
  "func.func"() <{sym_name = "shadow", function_type = (!llvm.ptr) -> (), sym_visibility = "private"}> ({}) : () -> ()

  "builtin.module"() ({
    "func.func"() <{sym_name = "nested_caller", function_type = (!llvm.ptr) -> ()}> ({
    ^bb0(%p: !llvm.ptr):
      "func.call"(%p) <{callee = @shadow}> : (!llvm.ptr) -> ()
      "func.call"(%p) <{callee = @byval}> : (!llvm.ptr) -> ()
      "func.return"() : () -> ()
    }) : () -> ()
    // CHECK-LABEL: "sym_name" = "nested_caller"
    // CHECK: "func.call"(%{{.*}}) <{"callee" = @shadow}> : (!llvm.ptr) -> ()
    // CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @byval}> : (!riscv.reg) -> ()
    // CHECK-NEXT: "riscv_cf.return"() : () -> ()
    "func.func"() <{sym_name = "shadow", function_type = (!llvm.ptr) -> (), arg_attrs = [{llvm.byval = i64}], sym_visibility = "private"}> ({}) : () -> ()
    // This ordinary local declaration shadows the unsupported outer one.
    "func.func"() <{sym_name = "byval", function_type = (!llvm.ptr) -> (), sym_visibility = "private"}> ({}) : () -> ()
  }) : () -> ()
}) : () -> ()
