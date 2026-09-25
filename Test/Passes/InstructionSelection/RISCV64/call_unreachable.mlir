// RUN: veir-opt %s -p=isel-br-riscv64 | filecheck %s

// Direct calls become `riscv_cf.call`, with their arguments cast to registers and
// their result cast back; `llvm.unreachable` becomes `riscv_cf.unreachable`. A
// call that `riscv_cf.call` might not pass correctly is left alone.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i64 (i64, !llvm.ptr)>}> ({
    ^bb0(%a : i64, %p : !llvm.ptr):
      %r = "llvm.call"(%a, %p) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.nonnull, llvm.noundef}], callee = @g, fastmathFlags = #llvm.fastmath<none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i64, !llvm.ptr) -> i64
      "llvm.call"() <{callee = @h}> : () -> ()
      %v = "llvm.call"(%p, %a) <{callee = @printf, var_callee_type = !llvm.func<i32 (ptr, ...)>}> : (!llvm.ptr, i64) -> i64
      %s = "llvm.add"(%r, %v) : (i64, i64) -> i64
      "llvm.return"(%s) : (i64) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "k", function_type = (i64) -> i64}> ({
    ^bb0(%a : i64):
      %r = "func.call"(%a) <{callee = @g}> : (i64) -> i64
      "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Narrow arguments are extended as the calling convention requires: by their
  // `signext` or `zeroext` attribute, and an `i32` with neither is sign-extended.
  // A narrow result is only truncated.
  "llvm.func"() <{sym_name = "narrow", function_type = !llvm.func<void (i32, i16, i8, i1)>}> ({
    ^bb0(%w : i32, %h : i16, %b : i8, %c : i1):
      "llvm.call"(%w) <{arg_attrs = [{llvm.noundef, llvm.signext}], callee = @g}> : (i32) -> ()
      "llvm.call"(%w) <{callee = @g}> : (i32) -> ()
      "llvm.call"(%w) <{arg_attrs = [{llvm.zeroext}], callee = @g}> : (i32) -> ()
      "llvm.call"(%h, %b) <{arg_attrs = [{llvm.signext}, {llvm.signext}], callee = @g}> : (i16, i8) -> ()
      "llvm.call"(%h, %b, %c) <{arg_attrs = [{llvm.zeroext}, {}, {llvm.zeroext}], callee = @g}> : (i16, i8, i1) -> ()
      %r = "llvm.call"() <{callee = @g, res_attrs = [{llvm.signext}]}> : () -> i32
      "llvm.return"() : () -> ()
  }) : () -> ()

  "llvm.func"() <{sym_name = "refused", function_type = !llvm.func<void (i64, i1, !llvm.ptr, i128)>}> ({
    ^bb0(%a : i64, %c : i1, %p : !llvm.ptr, %w : i128):
      // Indirect.
      "llvm.call"(%p) : (!llvm.ptr) -> ()
      // Nine arguments; the ninth would go on the stack.
      "llvm.call"(%a, %a, %a, %a, %a, %a, %a, %a, %a) <{callee = @g}> : (i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
      // Sign-extending an `i1` is not supported.
      "llvm.call"(%c) <{arg_attrs = [{llvm.signext}], callee = @g}> : (i1) -> ()
      // An `i128` takes two registers.
      "llvm.call"(%w) <{callee = @g}> : (i128) -> ()
      // `byval` passes a copy of the pointee, not the pointer.
      "llvm.call"(%p) <{arg_attrs = [{llvm.byval = i64}], callee = @g}> : (!llvm.ptr) -> ()
      // Some other calling convention.
      "llvm.call"(%a) <{CConv = #llvm.cconv<fastcc>, callee = @g}> : (i64) -> ()
      // A guaranteed tail call.
      "llvm.call"(%a) <{TailCallKind = #llvm.tailcallkind<musttail>, callee = @g}> : (i64) -> ()
      "llvm.return"() : () -> ()
  }) : () -> ()

  "llvm.func"() <{sym_name = "u", function_type = !llvm.func<void ()>}> ({
    ^bb0():
      "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[A:%[a-z0-9_]+]] : i64, [[P:%[a-z0-9_]+]] : !llvm.ptr):
// CHECK-NEXT:   [[RA:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[A]]) : (i64) -> !riscv.reg
// CHECK-NEXT:   [[RP:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[P]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:   [[CALL:%[a-z0-9_]+]] = "riscv_cf.call"([[RA]], [[RP]]) <{"callee" = @g}> : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:   [[R:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[CALL]]) : (!riscv.reg) -> i64
// CHECK-NEXT:   "riscv_cf.call"() <{"callee" = @h}> : () -> ()
// CHECK-NEXT:   [[VP:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[P]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:   [[VA:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[A]]) : (i64) -> !riscv.reg
// CHECK-NEXT:   [[VCALL:%[a-z0-9_]+]] = "riscv_cf.call"([[VP]], [[VA]]) <{"callee" = @printf}> : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:   [[V:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[VCALL]]) : (!riscv.reg) -> i64
// CHECK-NEXT:   [[S:%[a-z0-9_]+]] = "llvm.add"([[R]], [[V]]) : (i64, i64) -> i64
// CHECK-NEXT:   "llvm.return"([[S]]) : (i64) -> ()

// CHECK:      func.func @k([[KA:%[a-z0-9_]+]]: i64) -> i64 {
// CHECK-NEXT:   [[KR:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[KA]]) : (i64) -> !riscv.reg
// CHECK-NEXT:   [[KC:%[a-z0-9_]+]] = "riscv_cf.call"([[KR]]) <{"callee" = @g}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:   [[KB:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[KC]]) : (!riscv.reg) -> i64
// CHECK-NEXT:   "func.return"([[KB]]) : (i64) -> ()

// CHECK:      "sym_name" = "narrow"
// CHECK-NEXT: ^{{.*}}([[W:%[a-z0-9_]+]] : i32, [[H:%[a-z0-9_]+]] : i16, [[B:%[a-z0-9_]+]] : i8, [[C:%[a-z0-9_]+]] : i1):
// CHECK-NEXT:   [[W1:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[W]]) : (i32) -> !riscv.reg
// CHECK-NEXT:   [[W1S:%[a-z0-9_]+]] = "riscv.sextw"([[W1]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:   "riscv_cf.call"([[W1S]]) <{"callee" = @g}> : (!riscv.reg) -> ()
// CHECK-NEXT:   [[W2:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[W]]) : (i32) -> !riscv.reg
// CHECK-NEXT:   [[W2S:%[a-z0-9_]+]] = "riscv.sextw"([[W2]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:   "riscv_cf.call"([[W2S]]) <{"callee" = @g}> : (!riscv.reg) -> ()
// CHECK-NEXT:   [[W3:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[W]]) : (i32) -> !riscv.reg
// CHECK-NEXT:   "riscv_cf.call"([[W3]]) <{"callee" = @g}> : (!riscv.reg) -> ()
// CHECK-NEXT:   [[H1:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[H]]) : (i16) -> !riscv.reg
// CHECK-NEXT:   [[B1:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[B]]) : (i8) -> !riscv.reg
// CHECK-NEXT:   [[H1S:%[a-z0-9_]+]] = "riscv.sexth"([[H1]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:   [[B1S:%[a-z0-9_]+]] = "riscv.sextb"([[B1]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:   "riscv_cf.call"([[H1S]], [[B1S]]) <{"callee" = @g}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:   [[H2:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[H]]) : (i16) -> !riscv.reg
// CHECK-NEXT:   [[B2:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[B]]) : (i8) -> !riscv.reg
// CHECK-NEXT:   [[C2:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[C]]) : (i1) -> !riscv.reg
// CHECK-NEXT:   "riscv_cf.call"([[H2]], [[B2]], [[C2]]) <{"callee" = @g}> : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:   [[RC:%[a-z0-9_]+]] = "riscv_cf.call"() <{"callee" = @g}> : () -> !riscv.reg
// CHECK-NEXT:   "builtin.unrealized_conversion_cast"([[RC]]) : (!riscv.reg) -> i32
// CHECK-NEXT:   "llvm.return"() : () -> ()

// CHECK:      "sym_name" = "refused"
// CHECK-NOT:  riscv_cf.call
// CHECK:      "llvm.return"() : () -> ()

// CHECK:      "sym_name" = "u"
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT:   "riscv_cf.unreachable"() : () -> ()
