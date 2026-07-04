// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

// Note: `reconcile-cast` unconditionally coerces every function's register-width
// (i64/i32/`!llvm.ptr`) arguments to `!riscv.reg`, inserting a bridging cast at entry
// (see `coerce_function_boundaries.mlir`). Below, that boundary cast either reconciles
// away into the round trip already written in the body, or -- when it doesn't -- shows
// up as an extra leading cast. Functions whose argument is already `!riscv.reg` (or a
// non-coercible type like `i8`) are unaffected.

"builtin.module"() ({

  ^1():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   "test.test"([[C]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^2():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        "test.test"(%1) : (!riscv.reg) -> ()
        // The boundary's `reg -> i64` cast pairs with this body's `i64 -> reg` cast and
        // both reconcile away, leaving the register argument used directly.
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^3():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // the remaining cast is unused
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   "test.test"([[C]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^4():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // the remaining cast is used
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "test.test"(%1) : (!riscv.reg) -> (!riscv.reg)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i64
        "test.test"(%2, %3) : (!riscv.reg, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[I:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   [[T:%.*]] = "test.test"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"([[T]], [[I]]) : (!riscv.reg, i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^5():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // identity cast and pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> !riscv.reg
        %3 = "builtin.unrealized_conversion_cast"(%2) : (!riscv.reg) -> i64
        "test.test"(%3) : (i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   "test.test"([[C]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^6():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (!riscv.reg) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   "test.test"([[C]], [[C]]) : (i64, i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^7():
    "func.func"()  <{function_type = (!riscv.reg) -> ()}> ({
      ^1(%0 : !riscv.reg):
        // identity cast on block argument
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> !riscv.reg
        "test.test"(%1) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^8():
    "func.func"()  <{function_type = (i8) -> ()}> ({
      ^1(%0 : i8):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i8) -> i8
        "test.test"(%1) : (i8) -> ()
        // CHECK:        "test.test"(%{{.*}}) : (i8) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^9():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i256
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i128
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i256) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (i128) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   "test.test"([[C]], [[C]]) : (i64, i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^10():
    "func.func"()  <{function_type = (i32) -> ()}> ({
      ^1(%0 : i32):
        // i32 -> reg -> i32
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i32) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        "test.test"(%2) : (i32) -> ()
        // The `i32 -> reg -> i32` round trip reconciles regardless of which `i32` feeds
        // it, so this collapses to a single boundary `reg -> i32` cast.
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:   "test.test"([[C]]) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^11():
    "func.func"()  <{function_type = (!riscv.reg) -> ()}> ({
      ^1(%0 : !riscv.reg):
        // reg -> i32 -> reg : should not be folded away.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> i32
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   %[[C1:.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:   %[[C2:.*]] = "builtin.unrealized_conversion_cast"(%[[C1]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%[[C2]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^12():
    "func.func"()  <{function_type = (!llvm.ptr) -> ()}> ({
      ^1(%0 : !llvm.ptr):
        // ptr -> reg -> ptr (64-bit)
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!llvm.ptr) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> !llvm.ptr
        "test.test"(%2) : (!llvm.ptr) -> ()
        // The boundary's `reg -> ptr` cast pairs with the body's `ptr -> reg` cast (both
        // directions are legal for `ptr`), leaving one `reg -> ptr` cast.
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> !llvm.ptr
        // CHECK-NEXT:   "test.test"([[C]]) : (!llvm.ptr) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^13():
    "func.func"()  <{function_type = (!riscv.reg) -> ()}> ({
      ^1(%0 : !riscv.reg):
        // reg -> ptr -> reg (64-bit)
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> !llvm.ptr
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!llvm.ptr) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^14():
    "func.func"()  <{function_type = (i32) -> ()}> ({
      ^1(%0 : i32):
        // i32 -> reg -> i32  (reg is also used elsewhere)
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i32) -> !riscv.reg
        %2 = "test.test"(%1) : (!riscv.reg) -> (!riscv.reg)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        "test.test"(%2, %3) : (!riscv.reg, i32) -> ()
        // The boundary's `reg -> i32` cast (`[[NEW]]`) feeds the body's `i32 -> reg` cast
        // (`[[C1]]`); that pair is the protected `reg -> i32 -> reg` direction so it is
        // *not* reconciled, but `[[C1]]`'s other round trip back to `i32` still is, and
        // `[[C1]]` survives because `test.test` still uses it directly.
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[NEW:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[NEW]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:   [[C2:%.*]] = "test.test"([[C1]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"([[C2]], [[NEW]]) : (!riscv.reg, i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()



}) : () -> ()
