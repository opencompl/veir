// RUN: veir-interpret %s | filecheck %s

// `llvm.intr.fshr(a, b, c)` concatenates `a` (high) and `b` (low), shifts the
// double-width value right by `c` modulo the bit width, and returns the low
// half. When `a = b` it is a right rotate. Poison on any operand propagates.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i32, i32)}> ({
    %a = "llvm.mlir.constant"() <{ "value" = 0x12345678 : i32 }> : () -> i32
    %b = "llvm.mlir.constant"() <{ "value" = 0x9ABCDEF0 : i32 }> : () -> i32
    %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i32 }> : () -> i32
    %c0 = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    // 40 mod 32 == 8, so this matches the shift-by-8 case.
    %c40 = "llvm.mlir.constant"() <{ "value" = 40 : i32 }> : () -> i32
    %x = "llvm.mlir.constant"() <{ "value" = 0xF0000001 : i32 }> : () -> i32
    %c4 = "llvm.mlir.constant"() <{ "value" = 4 : i32 }> : () -> i32

    %p32 = "llvm.mlir.poison"() : () -> i32

    // Funnel shift right by 8.
    %r1 = "llvm.intr.fshr"(%a, %b, %c8) : (i32, i32, i32) -> i32
    // Shift amount of 0 returns `b` unchanged.
    %r2 = "llvm.intr.fshr"(%a, %b, %c0) : (i32, i32, i32) -> i32
    // Shift amount is taken modulo the bit width: 40 == 8.
    %r3 = "llvm.intr.fshr"(%a, %b, %c40) : (i32, i32, i32) -> i32
    // `a = b` is a right rotate by 4.
    %r4 = "llvm.intr.fshr"(%x, %x, %c4) : (i32, i32, i32) -> i32
    // Poison on any operand propagates.
    %r5 = "llvm.intr.fshr"(%a, %p32, %c8) : (i32, i32, i32) -> i32
    %r6 = "llvm.intr.fshr"(%a, %b, %p32) : (i32, i32, i32) -> i32

    "func.return"(%r1, %r2, %r3, %r4, %r5, %r6)
      : (i32, i32, i32, i32, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x789abcde#32, 0x9abcdef0#32, 0x789abcde#32, 0x1f000000#32, poison, poison]
