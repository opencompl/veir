// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// An `i64` `gmir.g_add` is selected as `riscv.addw` when all its users only read the low 32 bits,
// as LLVM's `binop_allwusers`.

"builtin.module"() ({
  // The only user is an `addw`, which reads the low 32 bits.
  // CHECK-LABEL: @w_user
  "func.func"() <{function_type = (i64, i64) -> i32, sym_name = "w_user"}> ({
  ^bb(%a: i64, %b: i64):
    %s = "gmir.g_add"(%a, %b) : (i64, i64) -> i64
    // CHECK:     "riscv.addw"
    // CHECK-NOT: "riscv.add"(
    %t = "llvm.trunc"(%s) : (i64) -> i32
    %u = "llvm.add"(%t, %t) : (i32, i32) -> i32
    // CHECK:     "riscv.addw"
    "func.return"(%u) : (i32) -> ()
  }) : () -> ()

  // The only user is a shift amount, which reads the low 6 bits.
  // CHECK-LABEL: @shamt_user
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "shamt_user"}> ({
  ^bb(%a: i64, %b: i64):
    %s = "gmir.g_add"(%a, %b) : (i64, i64) -> i64
    // CHECK:     "riscv.addw"
    %r = "llvm.shl"(%a, %s) : (i64, i64) -> i64
    // CHECK:     "riscv.sll"
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // `func.return` reads all 64 bits.
  // CHECK-LABEL: @full_user
  "func.func"() <{function_type = (i64, i64) -> (i32, i64), sym_name = "full_user"}> ({
  ^bb(%a: i64, %b: i64):
    %s = "gmir.g_add"(%a, %b) : (i64, i64) -> i64
    // CHECK:     "riscv.add"(
    // CHECK-NOT: "riscv.addw"
    %t = "llvm.trunc"(%s) : (i64) -> i32
    "func.return"(%t, %s) : (i32, i64) -> ()
  }) : () -> ()
}) : () -> ()
