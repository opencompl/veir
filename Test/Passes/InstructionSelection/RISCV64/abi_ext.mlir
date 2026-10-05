// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// `signext`/`zeroext` on returns and call arguments extend the value to the full
// register, matching `llc -mtriple=riscv64 -mattr=+zba,+zbb`. Without an attribute
// only an `i32` is extended (sign-extended, as the psABI requires); `zeroext i32` is
// zero-extended, as LLVM does even though the psABI sign-extends every 32-bit value.
// `reconcile-cast` may place a zero-extension in front of each of these, so the
// checks only pin the extension that feeds the return or call.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "ret_sext_i1", function_type = !llvm.func<i1 (i1)>, res_attrs = [{llvm.signext}]}> ({
  ^bb0(%x: i1):
    "llvm.return"(%x) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_sext_i1"
  // CHECK: %[[R:.*]] = "riscv.srai"(%{{.*}}) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: "riscv_cf.return"(%[[R]])

  "llvm.func"() <{sym_name = "ret_zext_i1", function_type = !llvm.func<i1 (i1)>, res_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%x: i1):
    "llvm.return"(%x) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_zext_i1"
  // CHECK: %[[R:.*]] = "riscv.andi"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: "riscv_cf.return"(%[[R]])

  "llvm.func"() <{sym_name = "ret_sext_i8", function_type = !llvm.func<i8 (i8)>, res_attrs = [{llvm.signext}]}> ({
  ^bb0(%x: i8):
    "llvm.return"(%x) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_sext_i8"
  // CHECK: %[[R:.*]] = "riscv.sextb"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.return"(%[[R]])

  "llvm.func"() <{sym_name = "ret_zext_i8", function_type = !llvm.func<i8 (i8)>, res_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%x: i8):
    "llvm.return"(%x) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_zext_i8"
  // CHECK: %[[R:.*]] = "riscv.zextb"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.return"(%[[R]])

  "llvm.func"() <{sym_name = "ret_any_i8", function_type = !llvm.func<i8 (i8)>}> ({
  ^bb0(%x: i8):
    "llvm.return"(%x) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_any_i8"
  // CHECK-NOT: riscv.sext
  // CHECK: "riscv_cf.return"

  "llvm.func"() <{sym_name = "ret_sext_i16", function_type = !llvm.func<i16 (i16)>, res_attrs = [{llvm.signext}]}> ({
  ^bb0(%x: i16):
    "llvm.return"(%x) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_sext_i16"
  // CHECK: %[[R:.*]] = "riscv.sexth"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.return"(%[[R]])

  "llvm.func"() <{sym_name = "ret_zext_i16", function_type = !llvm.func<i16 (i16)>, res_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%x: i16):
    "llvm.return"(%x) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_zext_i16"
  // CHECK: %[[R:.*]] = "riscv.zexth"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.return"(%[[R]])

  "llvm.func"() <{sym_name = "ret_any_i32", function_type = !llvm.func<i32 (i32)>}> ({
  ^bb0(%x: i32):
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_any_i32"
  // CHECK: %[[R:.*]] = "riscv.sextw"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.return"(%[[R]])

  "llvm.func"() <{sym_name = "ret_zext_i32", function_type = !llvm.func<i32 (i32)>, res_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%x: i32):
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "ret_zext_i32"
  // CHECK: %[[R:.*]] = "riscv.zextw"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.return"(%[[R]])

  "llvm.func"() <{sym_name = "arg_zext_i32", function_type = !llvm.func<void (i32)>, arg_attrs = [{llvm.zeroext}]}> ({
  ^bb0(%x: i32):
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "arg_zext_i32"
  // CHECK-NEXT: ^{{.*}}(%{{.*}} : !riscv.reg):
  // CHECK-NEXT: "riscv_cf.return"() : () -> ()

  // Declarations carrying the attributes: calls without them on the call site
  // fall back to the callee's.
  "llvm.func"() <{sym_name = "take_sext_i8", function_type = !llvm.func<void (i8)>, arg_attrs = [{llvm.signext}]}> ({
  }) : () -> ()
  "llvm.func"() <{sym_name = "take_zext_i16", function_type = !llvm.func<void (i16)>, arg_attrs = [{llvm.zeroext}]}> ({
  }) : () -> ()

  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<void (i1, i8, i16, i32)>}> ({
  ^bb0(%b: i1, %c: i8, %s: i16, %i: i32):
    %r1 = "llvm.call"(%b) <{callee = @ret_zext_i1, arg_attrs = [{llvm.zeroext}], res_attrs = [{llvm.zeroext}]}> : (i1) -> i1
    %r2 = "llvm.call"(%b) <{callee = @ret_sext_i1, arg_attrs = [{llvm.signext}], res_attrs = [{llvm.signext}]}> : (i1) -> i1
    %r3 = "llvm.call"(%c) <{callee = @ret_sext_i8, arg_attrs = [{llvm.signext}], res_attrs = [{llvm.signext}]}> : (i8) -> i8
    %r4 = "llvm.call"(%c) <{callee = @ret_any_i8}> : (i8) -> i8
    "llvm.call"(%c) <{callee = @take_sext_i8}> : (i8) -> ()
    "llvm.call"(%s) <{callee = @take_zext_i16}> : (i16) -> ()
    "llvm.call"(%i) <{callee = @arg_zext_i32, arg_attrs = [{llvm.zeroext}]}> : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "caller"
  // CHECK: %[[BZ:.*]] = "riscv.andi"(%{{.*}}) <{"value" = 1 : i64}>
  // CHECK-NEXT: "riscv_cf.call"(%[[BZ]]) <{"callee" = @ret_zext_i1}>
  // CHECK: %[[BS:.*]] = "riscv.srai"(%{{.*}}) <{"value" = 63 : i64}>
  // CHECK-NEXT: "riscv_cf.call"(%[[BS]]) <{"callee" = @ret_sext_i1}>
  // CHECK: %[[CS:.*]] = "riscv.sextb"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.call"(%[[CS]]) <{"callee" = @ret_sext_i8}>
  // CHECK-NOT: riscv.sext
  // CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @ret_any_i8}>
  // CHECK: %[[CS2:.*]] = "riscv.sextb"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.call"(%[[CS2]]) <{"callee" = @take_sext_i8}>
  // CHECK-NEXT: %[[SZ:.*]] = "riscv.zexth"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.call"(%[[SZ]]) <{"callee" = @take_zext_i16}>
  // CHECK: %[[IZ:.*]] = "riscv.zextw"(%{{.*}})
  // CHECK-NEXT: "riscv_cf.call"(%[[IZ]]) <{"callee" = @arg_zext_i32}>
  // CHECK-NEXT: "riscv_cf.return"() : () -> ()
}) : () -> ()
