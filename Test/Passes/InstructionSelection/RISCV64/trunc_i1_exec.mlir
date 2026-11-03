// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s --check-prefix=ISEL

// `trunc` to `i1` leaves the operand's upper bits in the register: 6 truncates to
// false, yet the register still holds 6. The `select` and the `cond_br` read the
// whole register, so they are only right if `reconcile-cast` zero-extends the `i1`
// before they use it. The false arms give 200 + 20 = 220 (0xdc).

// ISEL-NOT: "llvm.trunc"

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %six = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
      %t = "llvm.trunc"(%six) : (i64) -> i1
      %a = "llvm.mlir.constant"() <{value = 100 : i64}> : () -> i64
      %b = "llvm.mlir.constant"() <{value = 200 : i64}> : () -> i64
      %s = "llvm.select"(%t, %a, %b) : (i1, i64, i64) -> i64
      "llvm.cond_br"(%t) [^bb1, ^bb2] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb1():
      %c10 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
      %r1 = "llvm.add"(%s, %c10) : (i64, i64) -> i64
      "llvm.return"(%r1) : (i64) -> ()
    ^bb2():
      %c20 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
      %r2 = "llvm.add"(%s, %c20) : (i64, i64) -> i64
      "llvm.return"(%r2) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000000dc#64]
