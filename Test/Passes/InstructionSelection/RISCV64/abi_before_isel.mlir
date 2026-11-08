// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// ABI lowering must expose argument and call-result registers before instruction
// selection handles g_anyext. Otherwise selecting g_anyext inserts an iN -> reg
// cast, and ABI lowering later completes a reg -> iN -> reg round trip that
// reconcile-cast turns into a redundant zero-extension.

"builtin.module"() ({
  // Reversing the low 32 bits discards the input register's high bits. There
  // must be no zextw between the incoming argument and brev8.
  "llvm.func"() <{sym_name = "reverse32", function_type = !llvm.func<i32 (i32)>}> ({
  ^bb0(%x: i32):
    %r = "llvm.intr.bitreverse"(%x) : (i32) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "reverse32"
  // CHECK-NEXT: ^{{.*}}(%[[ARG:.*]] : !riscv.reg):
  // CHECK-NEXT: %[[BITS:.*]] = "riscv.brev8"(%[[ARG]])
  // CHECK-NEXT: %[[BYTES:.*]] = "riscv.rev8"(%[[BITS]])
  // CHECK-NEXT: %[[SHIFT:.*]] = "riscv.srli"(%[[BYTES]]) <{"value" = 32 : i64}>
  // CHECK-NEXT: %[[RESULT:.*]] = "riscv.sextw"(%[[SHIFT]])
  // CHECK-NEXT: "riscv_cf.return"(%[[RESULT]])

  "llvm.func"() <{sym_name = "source8", function_type = !llvm.func<i8 ()>}> ({
  }) : () -> ()

  // A sign-extension can consume the call's register directly, regardless of
  // its high bits; zero-extending the byte first would be redundant.
  "llvm.func"() <{sym_name = "signed_call8", function_type = !llvm.func<i64 ()>}> ({
    %x = "llvm.call"() <{callee = @source8}> : () -> i8
    %r = "llvm.sext"(%x) : (i8) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "signed_call8"
  // CHECK: %[[SIGNED_CALL:.*]] = "riscv_cf.call"() <{"callee" = @source8}>
  // CHECK-NEXT: %[[SIGNED:.*]] = "riscv.sextb"(%[[SIGNED_CALL]])
  // CHECK-NEXT: "riscv_cf.return"(%[[SIGNED]])

  // An explicit zero-extension still needs its mask: the call's upper bits
  // are unspecified. Reusing the register must not lose that requirement.
  "llvm.func"() <{sym_name = "unsigned_call8", function_type = !llvm.func<i64 ()>}> ({
    %x = "llvm.call"() <{callee = @source8}> : () -> i8
    %r = "llvm.zext"(%x) : (i8) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "unsigned_call8"
  // CHECK: %[[UNSIGNED_CALL:.*]] = "riscv_cf.call"() <{"callee" = @source8}>
  // CHECK-NEXT: %[[UNSIGNED:.*]] = "riscv.andi"(%[[UNSIGNED_CALL]]) <{"value" = 255 : i64}>
  // CHECK-NEXT: "riscv_cf.return"(%[[UNSIGNED]])
}) : () -> ()
