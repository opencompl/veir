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
    %c4 = "llvm.mlir.constant"() <{ "value" = 4 : i4 }> : () -> i4
    %cn6 = "llvm.mlir.constant"() <{ "value" = -6 : i4 }> : () -> i4
    %poison = "llvm.mlir.poison"() : () -> i8
    // 100 * 50 = 5000 = 0x1388; the high half is 0x13.
    %pos = "llvm.intr.umulh"(%c100, %c50) : (i8, i8) -> i8
    // The bits of -100 read unsigned are 156; 156 * 50 = 7800 = 0x1e78, so the
    // high half is 0x1e, where `llvm.intr.smulh` gives 0xec.
    %big = "llvm.intr.umulh"(%cn100, %c50) : (i8, i8) -> i8
    // 3 * 50 = 150 fits in 8 bits, so the high half is zero.
    %small = "llvm.intr.umulh"(%c3, %c50) : (i8, i8) -> i8
    // The LangRef example: umulh.i4(4, 10) = 2, the bits of -6 being 10.
    %narrow = "llvm.intr.umulh"(%c4, %cn6) : (i4, i4) -> i4
    // A poison operand gives poison.
    %p = "llvm.intr.umulh"(%c100, %poison) : (i8, i8) -> i8
    %c4000 = "llvm.mlir.constant"() <{ "value" = 4000 : i13 }> : () -> i13
    %cn4000 = "llvm.mlir.constant"() <{ "value" = -4000 : i13 }> : () -> i13
    %c4095 = "llvm.mlir.constant"() <{ "value" = 4095 : i13 }> : () -> i13
    %c3w = "llvm.mlir.constant"() <{ "value" = 3 : i13 }> : () -> i13
    // An odd width: the bits of -4000 read unsigned are 4192, and 4192 * 3 =
    // 12576 has high 13 bits 1, where `smulh` gives -2.
    %w1 = "llvm.intr.umulh"(%cn4000, %c3w) : (i13, i13) -> i13
    // 4095 * 4095 = 16769025, whose high 13 bits are 2047.
    %w2 = "llvm.intr.umulh"(%c4095, %c4095) : (i13, i13) -> i13
    "func.return"(%pos, %big, %small, %narrow, %p, %w1, %w2) : (i8, i8, i8, i4, i8, i13, i13) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x13#8, 0x1e#8, 0x00#8, 0x2#4, poison, 0x0001#13, 0x07ff#13]
// ALIVE_EXEC: Program output: #[poison, poison, poison, poison, poison, poison, poison]
// LLUBI_REJECTS: Unrecognized instruction: {{.*}}@llvm.umulh
