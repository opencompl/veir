// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A legal `g_store` is selected as `sb`, `sh`, `sw` or `sd`, which store the low bytes of the value.
"builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i64, !llvm.ptr) -> (), sym_name = "widths"}> ({
  ^bb0(%p: !llvm.ptr, %x: i64, %q: !llvm.ptr):
    // CHECK:      "riscv.sb"(%{{.*}}, %{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    // CHECK:      "riscv.sh"(%{{.*}}, %{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    // CHECK:      "riscv.sw"(%{{.*}}, %{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    // CHECK:      "riscv.sd"(%{{.*}}, %{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    // CHECK:      "riscv.sd"(%{{.*}}, %{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "gmir.g_store"(%x, %p) <{alignment = 1 : i64, size = 8 : i64}> : (i64, !llvm.ptr) -> ()
    "gmir.g_store"(%x, %p) <{alignment = 2 : i64, size = 16 : i64}> : (i64, !llvm.ptr) -> ()
    "gmir.g_store"(%x, %p) <{alignment = 4 : i64, size = 32 : i64}> : (i64, !llvm.ptr) -> ()
    "gmir.g_store"(%x, %p) <{alignment = 8 : i64, size = 64 : i64}> : (i64, !llvm.ptr) -> ()
    "gmir.g_store"(%q, %p) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
