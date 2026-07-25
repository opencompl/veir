// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Volatility survives instruction selection: the RISC-V encoding is identical
// either way, but the flag has to reach the riscv dialect so later passes know
// the access may not be deleted or duplicated.

"builtin.module"() ({
    // Volatile i64 load and store lower to `riscv.ld` / `riscv.sd` with the flag.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "vol"}> ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) <{"volatile_" = unit}> : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.ld"({{.*}}) <{"value" = 0 : i64, volatile_}> : (!riscv.reg) -> !riscv.reg
        "llvm.store"(%val, %a) <{"volatile_" = unit}> : (i64, !llvm.ptr) -> ()
        // CHECK:      "riscv.sd"({{.*}}) <{"value" = 0 : i64, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // The narrow widths carry it too.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "vol_narrow"}> ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) <{"volatile_" = unit}> : (!llvm.ptr) -> i32
        // CHECK:      {{.*}} = "riscv.lw"({{.*}}) <{"value" = 0 : i64, volatile_}> : (!riscv.reg) -> !riscv.reg
        %byte = "llvm.load"(%a) <{"volatile_" = unit}> : (!llvm.ptr) -> i8
        // CHECK:      {{.*}} = "riscv.lb"({{.*}}) <{"value" = 0 : i64, volatile_}> : (!riscv.reg) -> !riscv.reg
        "llvm.store"(%byte, %a) <{"volatile_" = unit}> : (i8, !llvm.ptr) -> ()
        // CHECK:      "riscv.sb"({{.*}}) <{"value" = 0 : i64, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // A non-volatile access lowers exactly as before: no flag is invented.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "plain"}> ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "riscv.ld"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        "llvm.store"(%val, %a) : (i64, !llvm.ptr) -> ()
        // CHECK:      "riscv.sd"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
