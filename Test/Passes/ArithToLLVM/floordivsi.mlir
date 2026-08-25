// RUN: veir-opt %s --mlir-print-op-generic -p=arith-to-llvm > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --check-prefix=LOWERED --input-file=%t

// Signed floor division rounds toward negative infinity. Cover all sign
// combinations, an exact negative quotient, a zero numerator, and both i8
// endpoints (without invoking the INT_MIN / -1 UB case).
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8, i8, i8)}> ({
    %c0 = "arith.constant"() <{value = 0 : i8}> : () -> i8
    %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %cn1 = "arith.constant"() <{value = -1 : i8}> : () -> i8
    %c2 = "arith.constant"() <{value = 2 : i8}> : () -> i8
    %cn2 = "arith.constant"() <{value = -2 : i8}> : () -> i8
    %c7 = "arith.constant"() <{value = 7 : i8}> : () -> i8
    %cn7 = "arith.constant"() <{value = -7 : i8}> : () -> i8
    %cn6 = "arith.constant"() <{value = -6 : i8}> : () -> i8
    %c127 = "arith.constant"() <{value = 127 : i8}> : () -> i8
    %cn128 = "arith.constant"() <{value = -128 : i8}> : () -> i8
    %r0 = "arith.floordivsi"(%c7, %c2) : (i8, i8) -> i8
    %r1 = "arith.floordivsi"(%cn7, %c2) : (i8, i8) -> i8
    %r2 = "arith.floordivsi"(%c7, %cn2) : (i8, i8) -> i8
    %r3 = "arith.floordivsi"(%cn7, %cn2) : (i8, i8) -> i8
    %r4 = "arith.floordivsi"(%cn6, %c2) : (i8, i8) -> i8
    %r5 = "arith.floordivsi"(%c0, %cn7) : (i8, i8) -> i8
    %r6 = "arith.floordivsi"(%c127, %cn1) : (i8, i8) -> i8
    %r7 = "arith.floordivsi"(%cn128, %c1) : (i8, i8) -> i8
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5, %r6, %r7)
      : (i8, i8, i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x03#8, 0xfc#8, 0xfc#8, 0x03#8, 0xfd#8, 0x00#8, 0x81#8, 0x80#8]

// LOWERED: "builtin.module"
// LOWERED-NOT: "arith.
