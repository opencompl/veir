// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// XFAIL: *
// Needs `split loads and stores (splitLoad, splitStore)`, commented out of the pass as unproven.

// Integers of 3, 5, 6 and 7 bytes are accessed in power-of-two pieces, widest
// first, and a volatile access keeps the flag on every piece.

"builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i24, i40, i48, i56) -> (), sym_name = "foo"}> ({
  ^bb0(%p: !llvm.ptr, %a: i24, %b: i40, %c: i48, %d: i56):
    // CHECK:      [[L0:%.*]] = "riscv.lhu"([[P:%.*]]) <{"value" = 0 : i64}>
    // CHECK-NEXT: [[L1:%.*]] = "riscv.lbu"([[P]]) <{"value" = 2 : i64}>
    // CHECK-NEXT: [[S1:%.*]] = "riscv.slli"([[L1]]) <{"value" = 16 : i64}>
    // CHECK-NEXT: {{%.*}} = "riscv.or"([[L0]], [[S1]])
    %l24 = "llvm.load"(%p) : (!llvm.ptr) -> i24
    // CHECK:      "riscv.lwu"({{.*}}) <{"value" = 0 : i64}>
    // CHECK-NEXT: "riscv.lbu"({{.*}}) <{"value" = 4 : i64}>
    // CHECK-NEXT: "riscv.slli"({{.*}}) <{"value" = 32 : i64}>
    // CHECK-NEXT: "riscv.or"
    %l40 = "llvm.load"(%p) : (!llvm.ptr) -> i40
    // CHECK:      "riscv.lwu"({{.*}}) <{"value" = 0 : i64}>
    // CHECK-NEXT: "riscv.lhu"({{.*}}) <{"value" = 4 : i64}>
    // CHECK-NEXT: "riscv.slli"({{.*}}) <{"value" = 32 : i64}>
    // CHECK-NEXT: "riscv.or"
    %l48 = "llvm.load"(%p) : (!llvm.ptr) -> i48
    // CHECK:      "riscv.lwu"({{.*}}) <{"value" = 0 : i64, volatile_}>
    // CHECK-NEXT: "riscv.lhu"({{.*}}) <{"value" = 4 : i64, volatile_}>
    // CHECK-NEXT: "riscv.slli"({{.*}}) <{"value" = 32 : i64}>
    // CHECK-NEXT: "riscv.or"
    // CHECK-NEXT: "riscv.lbu"({{.*}}) <{"value" = 6 : i64, volatile_}>
    // CHECK-NEXT: "riscv.slli"({{.*}}) <{"value" = 48 : i64}>
    // CHECK-NEXT: "riscv.or"
    %l56 = "llvm.load"(%p) <{volatile_}> : (!llvm.ptr) -> i56
    "test.test"(%l24, %l40, %l48, %l56) : (i24, i40, i48, i56) -> ()

    // CHECK:      "riscv.sh"([[V:%.*]], {{.*}}) <{"value" = 0 : i64}>
    // CHECK-NEXT: [[H:%.*]] = "riscv.srli"([[V]]) <{"value" = 16 : i64}>
    // CHECK-NEXT: "riscv.sb"([[H]], {{.*}}) <{"value" = 2 : i64}>
    "llvm.store"(%a, %p) : (i24, !llvm.ptr) -> ()
    // CHECK:      "riscv.sw"({{.*}}) <{"value" = 0 : i64}>
    // CHECK-NEXT: "riscv.srli"({{.*}}) <{"value" = 32 : i64}>
    // CHECK-NEXT: "riscv.sb"({{.*}}) <{"value" = 4 : i64}>
    "llvm.store"(%b, %p) : (i40, !llvm.ptr) -> ()
    // CHECK:      "riscv.sw"({{.*}}) <{"value" = 0 : i64}>
    // CHECK-NEXT: "riscv.srli"({{.*}}) <{"value" = 32 : i64}>
    // CHECK-NEXT: "riscv.sh"({{.*}}) <{"value" = 4 : i64}>
    "llvm.store"(%c, %p) : (i48, !llvm.ptr) -> ()
    // CHECK:      "riscv.sw"({{.*}}) <{"value" = 0 : i64, volatile_}>
    // CHECK-NEXT: "riscv.srli"({{.*}}) <{"value" = 32 : i64}>
    // CHECK-NEXT: "riscv.sh"({{.*}}) <{"value" = 4 : i64, volatile_}>
    // CHECK-NEXT: "riscv.srli"({{.*}}) <{"value" = 48 : i64}>
    // CHECK-NEXT: "riscv.sb"({{.*}}) <{"value" = 6 : i64, volatile_}>
    "llvm.store"(%d, %p) <{volatile_}> : (i56, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
