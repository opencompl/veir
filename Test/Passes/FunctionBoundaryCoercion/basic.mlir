// RUN: veir-opt %s -p=call-lowering-riscv64,reconcile-cast | filecheck %s

// XFAIL: *
// Needs `reconcileRegToPtr`, commented out of the pass as unproven.

// call-lowering-riscv64 coerces LLVM functions' register-width arguments and
// return values to `!riscv.reg`, inserting bridging casts and rewriting `function_type`,
// regardless of whether the body has actually been lowered by instruction selection yet
// (that's the caller's responsibility). For 64-bit boundaries (`i64`,
// `!llvm.ptr`) a round-trip already present in a lowered body becomes an identity that the
// pass removes; `i32` boundaries are copied with gMIR operations instead, which instruction
// selection lowers later (see `i32fn`). Returns of registers become `riscv_cf.return`.

"builtin.module"() ({

  // A Func function keeps its boundary even when its body contains RISC-V ops.
    "func.func"() <{sym_name = "lowered", function_type = (i64) -> i64}> ({
    ^bb(%a: i64):
      %r = "builtin.unrealized_conversion_cast"(%a) : (i64) -> !riscv.reg
      %s = "riscv.addi"(%r) <{value = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      %o = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> i64
      "func.return"(%o) : (i64) -> ()
      // CHECK:      func.func @lowered(%[[ARG:.*]]: i64) -> i64 {
      // CHECK-NEXT:   [[CAST:%.*]] = "builtin.unrealized_conversion_cast"(%[[ARG]]) : (i64) -> !riscv.reg
      // CHECK-NEXT:   [[R:%.*]] = "riscv.addi"([[CAST]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   [[RESULT:%.*]] = "builtin.unrealized_conversion_cast"([[R]]) : (!riscv.reg) -> i64
      // CHECK-NEXT:   "func.return"([[RESULT]]) : (i64) -> ()
    }) : () -> ()

  // `llvm.func` is lowered: the `i64` argument and result are coerced to
  // `!riscv.reg`, the `!llvm.func<...>` spelling is preserved, and `llvm.return`'s
  // operand is coerced.
    "llvm.func"() <{sym_name = "llvmlowered", function_type = !llvm.func<i64 (i64)>}> ({
    ^bb(%a: i64):
      %r = "builtin.unrealized_conversion_cast"(%a) : (i64) -> !riscv.reg
      %s = "riscv.addi"(%r) <{value = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      %o = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> i64
      "llvm.return"(%o) : (i64) -> ()
      // CHECK:      "llvm.func"() <{"function_type" = !llvm.func<!riscv.reg (!riscv.reg)>, "sym_name" = "llvmlowered"}>
      // CHECK-NEXT: ^{{.*}}([[LARG:%.*]] : !riscv.reg):
      // CHECK-NEXT:   [[LR:%.*]] = "riscv.addi"([[LARG]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   "riscv_cf.return"([[LR]]) : (!riscv.reg) -> ()
    }) : () -> ()

  // Pointers are 64-bit, so `!llvm.ptr` boundaries coerce to `!riscv.reg` too (the
  // `reg <-> ptr` round-trip is the identity and reconciles away).
    "llvm.func"() <{sym_name = "ptrfn", function_type = !llvm.func<ptr (ptr)>}> ({
    ^bb(%p: !llvm.ptr):
      %r = "builtin.unrealized_conversion_cast"(%p) : (!llvm.ptr) -> !riscv.reg
      %s = "riscv.addi"(%r) <{value = 8 : i64}> : (!riscv.reg) -> !riscv.reg
      %o = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> !llvm.ptr
      "llvm.return"(%o) : (!llvm.ptr) -> ()
      // CHECK:      "llvm.func"() <{"function_type" = !llvm.func<!riscv.reg (!riscv.reg)>, "sym_name" = "ptrfn"}>
      // CHECK-NEXT: ^{{.*}}([[PARG:%.*]] : !riscv.reg):
      // CHECK-NEXT:   [[PR:%.*]] = "riscv.addi"([[PARG]]) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   "riscv_cf.return"([[PR]]) : (!riscv.reg) -> ()
    }) : () -> ()

  // `i32` boundaries are coerced too (RISC-V passes/returns `int` in a register). The
  // argument is a `g_trunc` of the register's `i64`, and the psABI returns an `i32`
  // sign-extended, hence the `g_sext`.
    "llvm.func"() <{sym_name = "i32fn", function_type = !llvm.func<i32 (i32)>}> ({
    ^bb(%a: i32):
      %r = "builtin.unrealized_conversion_cast"(%a) : (i32) -> !riscv.reg
      %s = "riscv.addi"(%r) <{value = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      %o = "builtin.unrealized_conversion_cast"(%s) : (!riscv.reg) -> i32
      "llvm.return"(%o) : (i32) -> ()
      // CHECK:      "llvm.func"() <{"function_type" = !llvm.func<!riscv.reg (!riscv.reg)>, "sym_name" = "i32fn"}>
      // CHECK-NEXT: ^{{.*}}([[IARG:%.*]] : !riscv.reg):
      // CHECK-NEXT:   [[IW:%.*]] = "builtin.unrealized_conversion_cast"([[IARG]]) : (!riscv.reg) -> i64
      // CHECK-NEXT:   [[IT:%.*]] = "gmir.g_trunc"([[IW]]) : (i64) -> i32
      // CHECK-NEXT:   [[IR:%.*]] = "builtin.unrealized_conversion_cast"([[IT]]) : (i32) -> !riscv.reg
      // CHECK-NEXT:   [[IS:%.*]] = "riscv.addi"([[IR]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT:   [[IO:%.*]] = "builtin.unrealized_conversion_cast"([[IS]]) : (!riscv.reg) -> i32
      // CHECK-NEXT:   [[ISEXT:%.*]] = "gmir.g_sext"([[IO]]) : (i32) -> i64
      // CHECK-NEXT:   [[IRET:%.*]] = "builtin.unrealized_conversion_cast"([[ISEXT]]) : (i64) -> !riscv.reg
      // CHECK-NEXT:   "riscv_cf.return"([[IRET]]) : (!riscv.reg) -> ()
    }) : () -> ()

}) : () -> ()
