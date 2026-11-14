// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// RUN: ALIVE_EXEC_CHECK
// RUN: %if llubi-min-24 %{ LLUBI %}
// RUN: %if llubi-min-23 && !llubi-min-24 %{ not %llubi-interpret %s 2>&1 | filecheck %s --check-prefix=LLUBI_REJECTS %}

// llubi learned the intrinsic in LLVM 24; the LLVM 23 build it is pinned to
// still rejects the call, which the second RUN line holds it to. alive-exec
// does not know it either and evaluates it to poison. Pinning both, rather
// than opting out, makes a tool learning the intrinsic show up here.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i4, i8, i13, i13)}> ({
    %c100 = "llvm.mlir.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %c50 = "llvm.mlir.constant"() <{ "value" = 50 : i8 }> : () -> i8
    %cn100 = "llvm.mlir.constant"() <{ "value" = -100 : i8 }> : () -> i8
    %c3 = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %cn4 = "llvm.mlir.constant"() <{ "value" = -4 : i4 }> : () -> i4
    %c6 = "llvm.mlir.constant"() <{ "value" = 6 : i4 }> : () -> i4
    %poison = "llvm.mlir.poison"() : () -> i8
    // 100 * 50 = 5000 = 0x1388; the high half is 0x13.
    %pos = "llvm.intr.smulh"(%c100, %c50) : (i8, i8) -> i8
    // -100 * 50 = -5000 = 0xec78; the high half is 0xec, that is -20.
    %neg = "llvm.intr.smulh"(%cn100, %c50) : (i8, i8) -> i8
    // 3 * 50 = 150 fits in 8 bits, so the high half is zero.
    %small = "llvm.intr.smulh"(%c3, %c50) : (i8, i8) -> i8
    // The LangRef example: smulh.i4(-4, 6) = -2 = 0xe.
    %narrow = "llvm.intr.smulh"(%cn4, %c6) : (i4, i4) -> i4
    // A poison operand gives poison.
    %p = "llvm.intr.smulh"(%c100, %poison) : (i8, i8) -> i8
    %c4000 = "llvm.mlir.constant"() <{ "value" = 4000 : i13 }> : () -> i13
    %cn4000 = "llvm.mlir.constant"() <{ "value" = -4000 : i13 }> : () -> i13
    %c4095 = "llvm.mlir.constant"() <{ "value" = 4095 : i13 }> : () -> i13
    %c3w = "llvm.mlir.constant"() <{ "value" = 3 : i13 }> : () -> i13
    // An odd width: 4000 * 3 = 12000, whose high 13 bits are 1.
    %w1 = "llvm.intr.smulh"(%c4000, %c3w) : (i13, i13) -> i13
    // -4000 * 3 = -12000, whose high 13 bits are -2, where `umulh` gives 1.
    %w2 = "llvm.intr.smulh"(%cn4000, %c3w) : (i13, i13) -> i13
    "func.return"(%pos, %neg, %small, %narrow, %p, %w1, %w2) : (i8, i8, i8, i4, i8, i13, i13) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x13#8, 0xec#8, 0x00#8, 0xe#4, poison, 0x0001#13, 0x1ffe#13]
// ALIVE_EXEC: Program output: #[poison, poison, poison, poison, poison, poison, poison]
// LLUBI_REJECTS: Unrecognized instruction: {{.*}}@llvm.smulh
