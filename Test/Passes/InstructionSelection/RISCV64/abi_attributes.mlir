// RUN: veir-opt %s --print-op-generic -p=isel-abi-riscv64 | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// ABI attributes on either parameters or results prevent boundary lowering.
// In particular, byval and nest pointers must not become ordinary register arguments.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "byval_arg", function_type = !llvm.func<void (i64, ptr)>, arg_attrs = [{}, {llvm.byval = i64}]}> ({
  ^bb0(%n: i64, %p: !llvm.ptr):
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<void (i64, !llvm.ptr)>, "sym_name" = "byval_arg"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : i64, %{{.*}} : !llvm.ptr):
  // CHECK-NEXT: "llvm.return"() : () -> ()

  "llvm.func"() <{sym_name = "nest_arg", function_type = !llvm.func<i64 (ptr, i64)>, arg_attrs = [{llvm.nest}, {}]}> ({
  ^bb0(%env: !llvm.ptr, %n: i64):
    "llvm.return"(%n) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "arg_attrs" = [{llvm.nest}, {}], "function_type" = !llvm.func<i64 (!llvm.ptr, i64)>, "sym_name" = "nest_arg"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : !llvm.ptr, %[[NEST:.*]] : i64):
  // CHECK-NEXT: "llvm.return"(%[[NEST]]) : (i64) -> ()

  "llvm.func"() <{sym_name = "signext_arg", function_type = !llvm.func<i32 (i32)>, arg_attrs = [{llvm.signext}]}> ({
  ^bb0(%n: i32):
    "llvm.return"(%n) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<i32 (i32)>, "sym_name" = "signext_arg"
  // CHECK-NEXT: ^{{.*}}(%[[SA:.*]] : i32):
  // CHECK-NEXT: "llvm.return"(%[[SA]]) : (i32) -> ()

  "llvm.func"() <{sym_name = "zeroext_arg", function_type = !llvm.func<i32 (i32)>, arg_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%n: i32):
    "llvm.return"(%n) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<i32 (i32)>, "sym_name" = "zeroext_arg"
  // CHECK-NEXT: ^{{.*}}(%[[ZA:.*]] : i32):
  // CHECK-NEXT: "llvm.return"(%[[ZA]]) : (i32) -> ()

  "llvm.func"() <{sym_name = "signext_result", function_type = !llvm.func<i32 (i32)>, res_attrs = [{llvm.signext}]}> ({
  ^bb0(%n: i32):
    "llvm.return"(%n) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<i32 (i32)>, "res_attrs" = [{llvm.signext}], "sym_name" = "signext_result"
  // CHECK-NEXT: ^{{.*}}(%[[SR:.*]] : i32):
  // CHECK-NEXT: "llvm.return"(%[[SR]]) : (i32) -> ()

  "llvm.func"() <{sym_name = "zeroext_result", function_type = !llvm.func<i32 (i32)>, res_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%n: i32):
    "llvm.return"(%n) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<i32 (i32)>, "res_attrs" = [{llvm.zeroext}], "sym_name" = "zeroext_result"
  // CHECK-NEXT: ^{{.*}}(%[[ZR:.*]] : i32):
  // CHECK-NEXT: "llvm.return"(%[[ZR]]) : (i32) -> ()

  "func.func"() <{sym_name = "func_byval", function_type = (!llvm.ptr) -> (), arg_attrs = [{llvm.byval = i64}]}> ({
  ^bb0(%p: !llvm.ptr):
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = (!llvm.ptr) -> (), "sym_name" = "func_byval"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : !llvm.ptr):
  // CHECK-NEXT: "func.return"() : () -> ()

  "func.func"() <{sym_name = "func_nest", function_type = (!llvm.ptr, i64) -> i64, arg_attrs = [{llvm.nest}, {}]}> ({
  ^bb0(%env: !llvm.ptr, %n: i64):
    "func.return"(%n) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "arg_attrs" = [{llvm.nest}, {}], "function_type" = (!llvm.ptr, i64) -> i64, "sym_name" = "func_nest"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : !llvm.ptr, %[[FNEST:.*]] : i64):
  // CHECK-NEXT: "func.return"(%[[FNEST]]) : (i64) -> ()

  "func.func"() <{sym_name = "func_result", function_type = (i32) -> i32, res_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%n: i32):
    "func.return"(%n) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = (i32) -> i32, "res_attrs" = [{llvm.zeroext}], "sym_name" = "func_result"
  // CHECK-NEXT: ^{{.*}}(%[[FR:.*]] : i32):
  // CHECK-NEXT: "func.return"(%[[FR]]) : (i32) -> ()

  // An ordinary caller can still have its own boundary lowered, while calls
  // carrying these attributes retain their attributes and original types.
  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<void (i64, i32, ptr)>, arg_attrs = [{llvm.noundef}, {}, {}]}> ({
  ^bb0(%a: i64, %b: i32, %p: !llvm.ptr):
    "llvm.call"(%a, %p) <{callee = @byval_arg, arg_attrs = [{}, {llvm.byval = i64}]}> : (i64, !llvm.ptr) -> ()
    %nest = "llvm.call"(%p, %a) <{callee = @nest_arg, arg_attrs = [{llvm.nest}, {}]}> : (!llvm.ptr, i64) -> i64
    %fnest = "func.call"(%p, %nest) <{callee = @func_nest, arg_attrs = [{llvm.nest}, {}]}> : (!llvm.ptr, i64) -> i64
    %inest = "llvm.call"(%p, %p, %fnest) <{arg_attrs = [{llvm.nest}, {}]}> : (!llvm.ptr, !llvm.ptr, i64) -> i64
    %sa = "llvm.call"(%b) <{callee = @signext_arg, arg_attrs = [{llvm.signext}]}> : (i32) -> i32
    %za = "llvm.call"(%b) <{callee = @zeroext_arg, arg_attrs = [{llvm.zeroext}]}> : (i32) -> i32
    %sr = "llvm.call"(%b) <{callee = @signext_result, res_attrs = [{llvm.signext}]}> : (i32) -> i32
    %zr = "llvm.call"(%b) <{callee = @zeroext_result, res_attrs = [{llvm.zeroext}]}> : (i32) -> i32
    "func.call"(%p) <{callee = @func_byval, arg_attrs = [{llvm.byval = i64}]}> : (!llvm.ptr) -> ()
    %fr = "func.call"(%b) <{callee = @func_result, res_attrs = [{llvm.zeroext}]}> : (i32) -> i32
    %indirect = "llvm.call"(%p, %b) <{arg_attrs = [{llvm.signext}]}> : (!llvm.ptr, i32) -> i32
    // Unrelated attributes and empty dictionaries do not block lowering.
    %ok = "llvm.call"(%a) <{callee = @ordinary, arg_attrs = [{llvm.noundef}], res_attrs = [{}]}> : (i64) -> i64
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "function_type" = !llvm.func<void (!riscv.reg, !riscv.reg, !riscv.reg)>, "sym_name" = "caller"
  // CHECK: "llvm.call"(%{{.*}}, %{{.*}}) <{"arg_attrs" = [{}, {"llvm.byval" = i64}], "callee" = @byval_arg}> : (i64, !llvm.ptr) -> ()
  // CHECK-NEXT: %[[NCALL:.*]] = "llvm.call"(%{{.*}}, %{{.*}}) <{"arg_attrs" = [{llvm.nest}, {}], "callee" = @nest_arg}> : (!llvm.ptr, i64) -> i64
  // CHECK-NEXT: %[[FNCALL:.*]] = "func.call"(%{{.*}}, %[[NCALL]]) <{"arg_attrs" = [{llvm.nest}, {}], "callee" = @func_nest}> : (!llvm.ptr, i64) -> i64
  // CHECK-NEXT: %{{.*}} = "llvm.call"(%{{.*}}, %{{.*}}, %[[FNCALL]]) <{"arg_attrs" = [{llvm.nest}, {}]}> : (!llvm.ptr, !llvm.ptr, i64) -> i64
  // CHECK-NEXT: %{{.*}} = "llvm.call"(%{{.*}}) <{"arg_attrs" = [{llvm.signext}], "callee" = @signext_arg}> : (i32) -> i32
  // CHECK-NEXT: %{{.*}} = "llvm.call"(%{{.*}}) <{"arg_attrs" = [{llvm.zeroext}], "callee" = @zeroext_arg}> : (i32) -> i32
  // CHECK-NEXT: %{{.*}} = "llvm.call"(%{{.*}}) <{"callee" = @signext_result, "res_attrs" = [{llvm.signext}]}> : (i32) -> i32
  // CHECK-NEXT: %{{.*}} = "llvm.call"(%{{.*}}) <{"callee" = @zeroext_result, "res_attrs" = [{llvm.zeroext}]}> : (i32) -> i32
  // CHECK-NEXT: "func.call"(%{{.*}}) <{"arg_attrs" = [{"llvm.byval" = i64}], "callee" = @func_byval}> : (!llvm.ptr) -> ()
  // CHECK-NEXT: %{{.*}} = "func.call"(%{{.*}}) <{"callee" = @func_result, "res_attrs" = [{llvm.zeroext}]}> : (i32) -> i32
  // CHECK-NEXT: %{{.*}} = "llvm.call"(%{{.*}}, %{{.*}}) <{"arg_attrs" = [{llvm.signext}]}> : (!llvm.ptr, i32) -> i32
  // CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @ordinary}> : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: "riscv_cf.return"() : () -> ()
}) : () -> ()
