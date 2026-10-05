// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// Calls must honor ABI attributes found only on their callees, including
// declarations after the caller and discardable attributes. Quoted and escaped
// references must resolve to the same symbol as a bare reference.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<void (ptr)>}> ({
  ^bb0(%p: !llvm.ptr):
    "llvm.call"(%p) <{callee = @byval}> : (!llvm.ptr) -> ()
    "llvm.call"(%p) <{callee = @"byv\61l"}> : (!llvm.ptr) -> ()
    "llvm.call"() <{callee = @fast}> : () -> ()
    "llvm.call"(%p) <{callee = @discardable}> : (!llvm.ptr) -> ()
    "llvm.call"(%p) <{callee = @"nonutf8\FF"}> : (!llvm.ptr) -> ()
    // Supported declarations, unresolved external symbols, and indirect calls
    // remain eligible. An unsupported symbol in a nested module is unrelated.
    "llvm.call"(%p) <{callee = @ordinary}> : (!llvm.ptr) -> ()
    "llvm.call"() <{callee = @external}> : () -> ()
    "llvm.call"(%p) : (!llvm.ptr) -> ()
    "llvm.call"(%p) <{callee = @shadow}> : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "caller"
  // CHECK: "llvm.call"(%{{.*}}) <{"callee" = @byval}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: "llvm.call"(%{{.*}}) <{"callee" = @"byv\61l"}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: "llvm.call"() <{"callee" = @fast}> : () -> ()
  // CHECK-NEXT: "llvm.call"(%{{.*}}) <{"callee" = @discardable}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: "llvm.call"(%{{.*}}) <{"callee" = @"nonutf8\FF"}> : (!llvm.ptr) -> ()
  // CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @ordinary}> : (!riscv.reg) -> ()
  // CHECK: "riscv_cf.call"() <{"callee" = @external}> : () -> ()
  // CHECK: "riscv_cf.call"(%{{.*}}) : (!riscv.reg) -> ()
  // CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @shadow}> : (!riscv.reg) -> ()
  // CHECK-NEXT: "riscv_cf.return"() : () -> ()

  "llvm.func"() <{sym_name = "byval", function_type = !llvm.func<void (ptr)>, arg_attrs = [{llvm.byval = i64}], sym_visibility = "private"}> ({}) : () -> ()
  "llvm.func"() <{sym_name = "fast", function_type = !llvm.func<void ()>, CConv = #llvm.cconv<fastcc>}> ({}) : () -> ()
  "llvm.func"() <{sym_name = "discardable", function_type = !llvm.func<void (ptr)>, sym_visibility = "private"}> ({}) {arg_attrs = [{llvm.byval = i64}]} : () -> ()
  "llvm.func"() <{sym_name = "nonutf8\FF", function_type = !llvm.func<void (ptr)>, arg_attrs = [{llvm.byval = i64}], sym_visibility = "private"}> ({}) : () -> ()
  "llvm.func"() <{sym_name = "ordinary", function_type = !llvm.func<void (ptr)>, arg_attrs = [{llvm.noundef}], sym_visibility = "private"}> ({}) : () -> ()
  "llvm.func"() <{sym_name = "shadow", function_type = !llvm.func<void (ptr)>, sym_visibility = "private"}> ({}) : () -> ()

  "builtin.module"() ({
    "llvm.func"() <{sym_name = "nested_caller", function_type = !llvm.func<void (ptr)>}> ({
    ^bb0(%p: !llvm.ptr):
      "llvm.call"(%p) <{callee = @shadow}> : (!llvm.ptr) -> ()
      "llvm.call"(%p) <{callee = @byval}> : (!llvm.ptr) -> ()
      "llvm.return"() : () -> ()
    }) : () -> ()
    // CHECK-LABEL: "sym_name" = "nested_caller"
    // CHECK: "llvm.call"(%{{.*}}) <{"callee" = @shadow}> : (!llvm.ptr) -> ()
    // CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @byval}> : (!riscv.reg) -> ()
    // CHECK-NEXT: "riscv_cf.return"() : () -> ()
    "llvm.func"() <{sym_name = "shadow", function_type = !llvm.func<void (ptr)>, arg_attrs = [{llvm.byval = i64}], sym_visibility = "private"}> ({}) : () -> ()
    // This ordinary local declaration shadows the unsupported outer one.
    "llvm.func"() <{sym_name = "byval", function_type = !llvm.func<void (ptr)>, sym_visibility = "private"}> ({}) : () -> ()
  }) : () -> ()
}) : () -> ()
