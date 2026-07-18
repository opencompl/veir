// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

// Note: `reconcile-cast` unconditionally coerces every function's register-width
// (i64/i32/`!llvm.ptr`) arguments to `!riscv.reg`, inserting a bridging cast at entry
// (see `coerce_function_boundaries.mlir`). Below, that boundary cast either reconciles
// away into the round trip already written in the body, or -- when it doesn't -- shows
// up as an extra leading cast. Functions whose argument is already `!riscv.reg` (or a
// non-coercible type like `i8`) are unaffected.

"builtin.module"() ({

  ^1():
    "func.func"()  <{function_type = (i64) -> (), sym_name = "f0"}> ({
      ^1(%0 : i64):
        // A lone `iX -> iX` cast is not a round trip, so nothing reconciles it away.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   [[I:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i64) -> i64
        // CHECK-NEXT:   "test.test"([[I]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^2():
    "func.func"()  <{function_type = (i64) -> (), sym_name = "f1"}> ({
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
    "func.func"()  <{function_type = (i64) -> (), sym_name = "f2"}> ({
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
    "func.func"()  <{function_type = (i64) -> (), sym_name = "f3"}> ({
      ^1(%0 : i64):
        // the remaining cast is used
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "test.test"(%1) : (!riscv.reg) -> (!riscv.reg)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i64
        "test.test"(%2, %3) : (!riscv.reg, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[T:%.*]] = "test.test"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   [[I:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   "test.test"([[T]], [[I]]) : (!riscv.reg, i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^5():
    "func.func"()  <{function_type = (i64) -> (), sym_name = "f4"}> ({
      ^1(%0 : i64):
        // The `reg -> reg` cast in the middle breaks the `reg -> i64 -> reg` round trip: no
        // pair of adjacent casts returns to its own input type, so nothing reconciles.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> !riscv.reg
        %3 = "builtin.unrealized_conversion_cast"(%2) : (!riscv.reg) -> i64
        "test.test"(%3) : (i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[I:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[I]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   "test.test"([[C]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^6():
    "func.func"()  <{function_type = (i64) -> (), sym_name = "f5"}> ({
      ^1(%0 : i64):
        // pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (!riscv.reg) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // Each `i64 -> reg` cast folds to the register argument, leaving the two `reg -> i64`
        // casts behind as separate (identical) operations.
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   [[C2:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   "test.test"([[C1]], [[C2]]) : (i64, i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^7():
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "f6"}> ({
      ^1(%0 : !riscv.reg):
        // identity cast on block argument: not a round trip, so it survives the pass
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> !riscv.reg
        "test.test"(%1) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[I:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"([[I]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^8():
    "func.func"()  <{function_type = (i8) -> (), sym_name = "f7"}> ({
      ^1(%0 : i8):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i8) -> i8
        "test.test"(%1) : (i8) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i8):
        // CHECK-NEXT:   [[I:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (i8) -> i8
        // CHECK-NEXT:   "test.test"([[I]]) : (i8) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^9():
    "func.func"()  <{function_type = (i64) -> (), sym_name = "f8"}> ({
      ^1(%0 : i64):
        // `iX -> iY -> iX` round trips are not reconciled: the interpreter gives an
        // integer-to-integer cast no semantics, so the pass leaves these alone.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i256
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i128
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i256) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (i128) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:   [[W1:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i64) -> i256
        // CHECK-NEXT:   [[W2:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i64) -> i128
        // CHECK-NEXT:   [[N1:%.*]] = "builtin.unrealized_conversion_cast"([[W1]]) : (i256) -> i64
        // CHECK-NEXT:   [[N2:%.*]] = "builtin.unrealized_conversion_cast"([[W2]]) : (i128) -> i64
        // CHECK-NEXT:   "test.test"([[N1]], [[N2]]) : (i64, i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^10():
    "func.func"()  <{function_type = (i32) -> (), sym_name = "f9"}> ({
      ^1(%0 : i32):
        // i32 -> reg -> i32
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i32) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        "test.test"(%2) : (i32) -> ()
        // The `i32 -> reg -> i32` round trip is not itself reconciled (it freezes poison), but
        // the boundary's `reg -> i32` cast forms a `reg -> i32 -> reg` round trip with the body's
        // first cast, which lowers to `zextw`. The body's second cast remains.
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[Z:%.*]] = "riscv.zextw"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[Z]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:   "test.test"([[C]]) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^11():
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "f10"}> ({
      ^1(%0 : !riscv.reg):
        // reg -> i32 -> reg : should not be folded away.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> i32
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   %[[C1:.*]] = "riscv.zextw"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%[[C1]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^12():
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "f11"}> ({
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
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "f12"}> ({
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
    "func.func"()  <{function_type = (i32) -> (), sym_name = "f13"}> ({
      ^1(%0 : i32):
        // i32 -> reg -> i32  (reg is also used elsewhere)
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i32) -> !riscv.reg
        %2 = "test.test"(%1) : (!riscv.reg) -> (!riscv.reg)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        "test.test"(%2, %3) : (!riscv.reg, i32) -> ()
        // The boundary's `reg -> i32` cast feeds the body's `i32 -> reg` cast, and that
        // `reg -> i32 -> reg` round trip lowers to an explicit `zextw`. The body's second
        // cast then reads the `zextw` result directly.
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   [[Z:%.*]] = "riscv.zextw"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   [[T:%.*]] = "test.test"([[Z]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   [[C:%.*]] = "builtin.unrealized_conversion_cast"([[Z]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:   "test.test"([[T]], [[C]]) : (!riscv.reg, i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^15():
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "f14"}> ({
      ^1(%0 : !riscv.reg):
        // reg -> i16 -> reg : should not be folded away.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> i16
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i16) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   %[[C1:.*]] = "riscv.zexth"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%[[C1]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    
  ^16():
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "f15"}> ({
      ^1(%0 : !riscv.reg):
        // reg -> i8 -> reg : should not be folded away.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> i8
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i8) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   %[[C1:.*]] = "riscv.zextb"([[ARG]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%[[C1]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^17():
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "f16"}> ({
      ^1(%0 : !riscv.reg):
        // reg -> i14 -> reg : should not be folded away.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> i14
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i14) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   %[[C1:.*]] = "riscv.slli"([[ARG]]) <{"value" = 50 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   %[[C2:.*]] = "riscv.srli"(%[[C1]]) <{"value" = 50 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%[[C2]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^18():
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "f17"}> ({
      ^1(%0 : !riscv.reg):
        // reg -> i0 -> reg : the round trip is the constant zero, which the `slli`/`srli`
        // pair cannot compute (its 6-bit shift amount `64 - 0` wraps back to `0`).
        // The casts must be left alone.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> i0
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i0) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   %[[C1:.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i0
        // CHECK-NEXT:   %[[C2:.*]] = "builtin.unrealized_conversion_cast"(%[[C1]]) : (i0) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%[[C2]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
