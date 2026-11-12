// RUN: veir-opt %s -p=riscv > %t
// RUN: veir2mir %t | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "bitreverse_8", function_type = !llvm.func<i8 (i8)>}> ({
  ^bb0(%x: i8):
    %r = "llvm.intr.bitreverse"(%x) : (i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: name: bitreverse_8
  // CHECK: BREV8
  // CHECK: PseudoRET
  // CHECK-NOT: UNHANDLED
  "llvm.func"() <{sym_name = "bswap_16", function_type = !llvm.func<i16 (i16)>}> ({
  ^bb0(%x: i16):
    %r = "llvm.intr.bswap"(%x) : (i16) -> i16
    "llvm.return"(%r) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: name: bswap_16
  // CHECK: REV8_RV64
  // CHECK: SRLI {{.*}}, 48
  // CHECK: PseudoRET
  // CHECK-NOT: UNHANDLED
  "llvm.func"() <{sym_name = "bitreverse_16", function_type = !llvm.func<i16 (i16)>}> ({
  ^bb0(%x: i16):
    %r = "llvm.intr.bitreverse"(%x) : (i16) -> i16
    "llvm.return"(%r) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: name: bitreverse_16
  // CHECK: BREV8
  // CHECK: REV8_RV64
  // CHECK: SRLI {{.*}}, 48
  // CHECK: PseudoRET
  // CHECK-NOT: UNHANDLED
  "llvm.func"() <{sym_name = "bswap_32", function_type = !llvm.func<i32 (i32)>}> ({
  ^bb0(%x: i32):
    %r = "llvm.intr.bswap"(%x) : (i32) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: name: bswap_32
  // CHECK: REV8_RV64
  // CHECK: SRLI {{.*}}, 32
  // CHECK: PseudoRET
  // CHECK-NOT: UNHANDLED
  "llvm.func"() <{sym_name = "bitreverse_32", function_type = !llvm.func<i32 (i32)>}> ({
  ^bb0(%x: i32):
    %r = "llvm.intr.bitreverse"(%x) : (i32) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: name: bitreverse_32
  // CHECK: BREV8
  // CHECK: REV8_RV64
  // CHECK: SRLI {{.*}}, 32
  // CHECK: PseudoRET
  // CHECK-NOT: UNHANDLED
  "llvm.func"() <{sym_name = "bswap_64", function_type = !llvm.func<i64 (i64)>}> ({
  ^bb0(%x: i64):
    %r = "llvm.intr.bswap"(%x) : (i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: name: bswap_64
  // CHECK: REV8_RV64
  // CHECK: PseudoRET
  // CHECK-NOT: UNHANDLED
  "llvm.func"() <{sym_name = "bitreverse_64", function_type = !llvm.func<i64 (i64)>}> ({
  ^bb0(%x: i64):
    %r = "llvm.intr.bitreverse"(%x) : (i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: name: bitreverse_64
  // CHECK: BREV8
  // CHECK: REV8_RV64
  // CHECK: PseudoRET
  // CHECK-NOT: UNHANDLED
}) : () -> ()
