// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,isel-riscv64,reconcile-cast | filecheck %s

// Selecting pointers lowers exactly like selecting `i64`s: a pointer fills a whole register.

"builtin.module"() ({
  "func.func"() <{function_type = (i1, !llvm.ptr, !llvm.ptr) -> (), sym_name = "foo"}> ({
  ^bb0(%c: i1, %t: !llvm.ptr, %f: !llvm.ptr):
    // CHECK:      [[C:%.*]] = "riscv.andi"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: [[T:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
    // CHECK-NEXT: [[F:%.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
    // CHECK-NEXT: [[A:%.*]] = "riscv.czeroeqz"([[T]], [[C]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: [[B:%.*]] = "riscv.czeronez"([[F]], [[C]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: [[R:%.*]] = "riscv.or"([[A]], [[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: [[P:%.*]] = "builtin.unrealized_conversion_cast"([[R]]) : (!riscv.reg) -> !llvm.ptr
    // CHECK-NEXT: "test.test"([[P]]) : (!llvm.ptr) -> ()
    %r = "llvm.select"(%c, %t, %f) : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "test.test"(%r) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
