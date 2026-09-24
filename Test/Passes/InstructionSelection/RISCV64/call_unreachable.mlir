// RUN: veir-opt %s -p=isel-br-riscv64 | filecheck %s

// Direct calls become `riscv_cf.call`, with their arguments cast to registers and
// their result cast back; `llvm.unreachable` becomes `riscv_cf.unreachable`. An
// indirect call is left alone.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i64 (i64, i32, !llvm.ptr)>}> ({
    ^bb0(%a : i64, %b : i32, %p : !llvm.ptr):
      %r = "llvm.call"(%a, %b) <{callee = @g}> : (i64, i32) -> i64
      "llvm.call"() <{callee = @h}> : () -> ()
      "llvm.call"(%p) : (!llvm.ptr) -> ()
      %s = "llvm.add"(%r, %r) : (i64, i64) -> i64
      "llvm.return"(%s) : (i64) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "k", function_type = (i64) -> i64}> ({
    ^bb0(%a : i64):
      %r = "func.call"(%a) <{callee = @g}> : (i64) -> i64
      "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  "llvm.func"() <{sym_name = "u", function_type = !llvm.func<void ()>}> ({
    ^bb0():
      "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[A:%[a-z0-9_]+]] : i64, [[B:%[a-z0-9_]+]] : i32, [[P:%[a-z0-9_]+]] : !llvm.ptr):
// CHECK-NEXT:   [[RA:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[A]]) : (i64) -> !riscv.reg
// CHECK-NEXT:   [[RB:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[B]]) : (i32) -> !riscv.reg
// CHECK-NEXT:   [[CALL:%[a-z0-9_]+]] = "riscv_cf.call"([[RA]], [[RB]]) <{"callee" = @g}> : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:   [[R:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[CALL]]) : (!riscv.reg) -> i64
// CHECK-NEXT:   "riscv_cf.call"() <{"callee" = @h}> : () -> ()
// CHECK-NEXT:   "llvm.call"([[P]]) : (!llvm.ptr) -> ()
// CHECK-NEXT:   [[S:%[a-z0-9_]+]] = "llvm.add"([[R]], [[R]]) : (i64, i64) -> i64
// CHECK-NEXT:   "llvm.return"([[S]]) : (i64) -> ()

// CHECK:      func.func @k([[KA:%[a-z0-9_]+]]: i64) -> i64 {
// CHECK-NEXT:   [[KR:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[KA]]) : (i64) -> !riscv.reg
// CHECK-NEXT:   [[KC:%[a-z0-9_]+]] = "riscv_cf.call"([[KR]]) <{"callee" = @g}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:   [[KB:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[KC]]) : (!riscv.reg) -> i64
// CHECK-NEXT:   "func.return"([[KB]]) : (i64) -> ()

// CHECK:      "sym_name" = "u"
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT:   "riscv_cf.unreachable"() : () -> ()
