// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A legal `g_load` is selected as LLVM selects the any-extending load of its size:
// `lbu`, `lh`, `lw` or `ld`.
"builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "widths"}> ({
  ^bb0(%p: !llvm.ptr):
    // CHECK:      "riscv.lbu"(%{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    // CHECK:      "riscv.lh"(%{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    // CHECK:      "riscv.lw"(%{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    // CHECK:      "riscv.ld"(%{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    // CHECK:      "riscv.ld"(%{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr
    %a = "gmir.g_load"(%p) <{alignment = 1 : i64, size = 8 : i64}> : (!llvm.ptr) -> i64
    %b = "gmir.g_load"(%p) <{alignment = 2 : i64, size = 16 : i64}> : (!llvm.ptr) -> i64
    %c = "gmir.g_load"(%p) <{alignment = 4 : i64, size = 32 : i64}> : (!llvm.ptr) -> i64
    %d = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr) -> i64
    %e = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr) -> !llvm.ptr
    "test.test"(%a, %b, %c, %d, %e) : (i64, i64, i64, i64, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // A constant `getelementptr` offset is folded into the immediate: i32 element, index 2 -> 8.
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "offset"}> ({
  ^bb0(%p: !llvm.ptr):
    %i = "gmir.g_constant"() <{value = 2 : i64}> : () -> i64
    %g = "llvm.getelementptr"(%p, %i) <{elem_type = i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    // CHECK:      "riscv.lw"(%{{.*}}) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
    %v = "gmir.g_load"(%g) <{alignment = 4 : i64, size = 32 : i64}> : (!llvm.ptr) -> i64
    "test.test"(%v) : (i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // A volatile load stays volatile.
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "volatile"}> ({
  ^bb0(%p: !llvm.ptr):
    // CHECK:      "riscv.ld"(%{{.*}}) <{"value" = 0 : i64, volatile_}> : (!riscv.reg) -> !riscv.reg
    %v = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 64 : i64, volatile_}> : (!llvm.ptr) -> i64
    "test.test"(%v) : (i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  // Illegal loads are not selected.
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "illegal"}> ({
  ^bb0(%p: !llvm.ptr):
    // CHECK:      "gmir.g_load"(%{{.*}}) <{"alignment" = 1 : i64, "size" = 16 : i64}> : (!llvm.ptr) -> i64
    // CHECK-NEXT: "gmir.g_load"(%{{.*}}) <{"alignment" = 1 : i64, "size" = 8 : i64}> : (!llvm.ptr) -> i8
    %a = "gmir.g_load"(%p) <{alignment = 1 : i64, size = 16 : i64}> : (!llvm.ptr) -> i64
    %b = "gmir.g_load"(%p) <{alignment = 1 : i64, size = 8 : i64}> : (!llvm.ptr) -> i8
    "test.test"(%a, %b) : (i64, i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
