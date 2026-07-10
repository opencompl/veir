// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

// The cast-reconciliation pass coerces every function's register-width arguments and
// return values to `!riscv.reg`, inserting bridging casts and rewriting `function_type`,
// regardless of whether the body has actually been lowered by instruction selection yet
// (that's the caller's responsibility -- see `notlowered`). For 64-bit boundaries (`i64`,
// `!llvm.ptr`) a round-trip already present in a lowered body becomes an identity that the
// pass removes; for `i32` boundaries the round-trip truncates and is instead reconciled
// into an explicit `zextw` (see `i32fn`).

"builtin.module"() ({

  // A lowered function (it contains a `riscv.addi`): its `i64` argument and result
  // are coerced to `!riscv.reg`, and the reg<->i64 round-trip casts are removed, so
  // the `riscv.addi` consumes the register argument directly.
    "func.func"() <{sym_name = "lowered", function_type = (i64) -> i64}> ({
    ^bb(%a: i64):
      %r = "builtin.unrealized_conversion_cast"(%a) : (i64) -> !riscv.reg
      %s = "riscv.addi"(%r) <{value = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      %o = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> i64
      "func.return"(%o) : (i64) -> ()
      // CHECK:      "func.func"() <{"function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "lowered"}>
      // CHECK-NEXT: ^{{.*}}([[ARG:%.*]] : !riscv.reg):
      // CHECK-NEXT:   [[R:%.*]] = "riscv.addi"([[ARG]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   "func.return"([[R]]) : (!riscv.reg) -> ()
    }) : () -> ()

  // `llvm.func` is handled too: the `i64` argument and result are coerced to
  // `!riscv.reg`, the `!llvm.func<...>` spelling is preserved, and `llvm.return`'s
  // operand is coerced. i32 boundaries would be left untouched (unsound to reconcile).
    "llvm.func"() <{sym_name = "llvmlowered", function_type = !llvm.func<i64 (i64)>}> ({
    ^bb(%a: i64):
      %r = "builtin.unrealized_conversion_cast"(%a) : (i64) -> !riscv.reg
      %s = "riscv.addi"(%r) <{value = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      %o = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> i64
      "llvm.return"(%o) : (i64) -> ()
      // CHECK:      "llvm.func"() <{"function_type" = !llvm.func<!riscv.reg (!riscv.reg)>, "sym_name" = "llvmlowered"}>
      // CHECK-NEXT: ^{{.*}}([[LARG:%.*]] : !riscv.reg):
      // CHECK-NEXT:   [[LR:%.*]] = "riscv.addi"([[LARG]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   "llvm.return"([[LR]]) : (!riscv.reg) -> ()
    }) : () -> ()

  // Pointers are 64-bit, so `!llvm.ptr` boundaries coerce to `!riscv.reg` too (the
  // `reg <-> ptr` round-trip is the identity and reconciles away).
    "func.func"() <{sym_name = "ptrfn", function_type = (!llvm.ptr) -> !llvm.ptr}> ({
    ^bb(%p: !llvm.ptr):
      %r = "builtin.unrealized_conversion_cast"(%p) : (!llvm.ptr) -> !riscv.reg
      %s = "riscv.addi"(%r) <{value = 8 : i64}> : (!riscv.reg) -> !riscv.reg
      %o = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> !llvm.ptr
      "func.return"(%o) : (!llvm.ptr) -> ()
      // CHECK:      "func.func"() <{"function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "ptrfn"}>
      // CHECK-NEXT: ^{{.*}}([[PARG:%.*]] : !riscv.reg):
      // CHECK-NEXT:   [[PR:%.*]] = "riscv.addi"([[PARG]]) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   "func.return"([[PR]]) : (!riscv.reg) -> ()
    }) : () -> ()

  // `i32` boundaries are coerced too (RISC-V passes/returns `int` in a register), but the
  // `reg <-> i32` round-trip truncates rather than being the identity, so the reconciliation
  // patterns do *not* simply erase it: the `function_type` becomes `(!riscv.reg) -> !riscv.reg`
  // while the residual `reg -> i32 -> reg` truncation on both the argument and the return
  // operand is reconciled into an explicit `zextw`.
    "func.func"() <{sym_name = "i32fn", function_type = (i32) -> i32}> ({
    ^bb(%a: i32):
      %r = "builtin.unrealized_conversion_cast"(%a) : (i32) -> !riscv.reg
      %s = "riscv.addi"(%r) <{value = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      %o = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> i32
      "func.return"(%o) : (i32) -> ()
      // CHECK:      "func.func"() <{"function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "i32fn"}>
      // CHECK-NEXT: ^{{.*}}([[IARG:%.*]] : !riscv.reg):
      // CHECK-NEXT:   [[IZ:%.*]] = "riscv.zextw"([[IARG]]) : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   [[IS:%.*]] = "riscv.addi"([[IZ]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   [[IRET:%.*]] = "riscv.zextw"([[IS]]) : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   "func.return"([[IRET]]) : (!riscv.reg) -> ()
    }) : () -> ()

}) : () -> ()
