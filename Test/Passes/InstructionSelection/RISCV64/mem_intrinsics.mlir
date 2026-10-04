// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A constant-length memcpy/memset that takes at most 8 accesses, each no wider
// than the known alignment, is expanded into loads and stores. Anything else
// becomes a call to the C library function.

"builtin.module"() ({
  // 7 bytes, align 4 (the smaller of the two arguments): word, half, byte.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "cpy7_a4"}> ({
  ^bb0(%d: !llvm.ptr, %s: !llvm.ptr):
    %n = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.intr.memcpy"(%d, %s, %n) <{arg_attrs = [{llvm.align = 4 : i64}, {llvm.align = 8 : i64}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "cpy7_a4"
  // CHECK:      %[[W:.*]] = "riscv.lw"(%[[S:.*]]) <{"value" = 0 : i64}>
  // CHECK-NEXT: "riscv.sw"(%[[W]], %[[D:.*]]) <{"value" = 0 : i64}>
  // CHECK-NEXT: %[[H:.*]] = "riscv.lh"(%[[S]]) <{"value" = 4 : i64}>
  // CHECK-NEXT: "riscv.sh"(%[[H]], %[[D]]) <{"value" = 4 : i64}>
  // CHECK-NEXT: %[[B:.*]] = "riscv.lb"(%[[S]]) <{"value" = 6 : i64}>
  // CHECK-NEXT: "riscv.sb"(%[[B]], %[[D]]) <{"value" = 6 : i64}>
  // CHECK-NEXT: "llvm.return"

  // 64 bytes, align 8: eight doublewords.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "cpy64_a8"}> ({
  ^bb0(%d: !llvm.ptr, %s: !llvm.ptr):
    %n = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    "llvm.intr.memcpy"(%d, %s, %n) <{arg_attrs = [{llvm.align = 8 : i64}, {llvm.align = 8 : i64}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "cpy64_a8"
  // CHECK-NOT:  riscv_cf.call
  // CHECK:      "riscv.sd"({{.*}}) <{"value" = 56 : i64}>
  // CHECK-NEXT: "llvm.return"

  // 9 bytes, unknown alignment: more than 8 byte accesses, so a call.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "cpy9"}> ({
  ^bb0(%d: !llvm.ptr, %s: !llvm.ptr):
    %n = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    "llvm.intr.memcpy"(%d, %s, %n) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "cpy9"
  // CHECK:      %[[N:.*]] = "riscv.li"() <{"value" = 9 : i64}>
  // CHECK-NEXT: %[[NI:.*]] = "builtin.unrealized_conversion_cast"(%[[N]]) : (!riscv.reg) -> i64
  // CHECK:      %[[NR:.*]] = "builtin.unrealized_conversion_cast"(%[[NI]]) : (i64) -> !riscv.reg
  // CHECK-NEXT: "riscv_cf.call"(%{{.*}}, %{{.*}}, %[[NR]]) <{"callee" = @memcpy}> : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()

  // Non-constant length: a call.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "cpyn"}> ({
  ^bb0(%d: !llvm.ptr, %s: !llvm.ptr, %n: i64):
    "llvm.intr.memcpy"(%d, %s, %n) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "cpyn"
  // CHECK:      "riscv_cf.call"(%{{.*}}, %{{.*}}, %{{.*}}) <{"callee" = @memcpy}>

  // Volatile zero memset: the accesses stay volatile.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "zero16_a8_volatile"}> ({
  ^bb0(%d: !llvm.ptr):
    %n = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %z = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    "llvm.intr.memset"(%d, %z, %n) <{arg_attrs = [{llvm.align = 8 : i64}, {}, {}], isVolatile = true}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "zero16_a8_volatile"
  // CHECK:      %[[Z:.*]] = "riscv.li"() <{"value" = 0 : i64}>
  // CHECK-NEXT: "riscv.sd"(%[[Z]], %[[D:.*]]) <{"value" = 0 : i64, volatile_}>
  // CHECK-NEXT: "riscv.sd"(%[[Z]], %[[D]]) <{"value" = 8 : i64, volatile_}>
  // CHECK-NEXT: "llvm.return"

  // Constant fill: one splat constant, narrower stores take its low bits.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "set6_a2"}> ({
  ^bb0(%d: !llvm.ptr):
    %n = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %c = "llvm.mlir.constant"() <{value = -86 : i8}> : () -> i8
    "llvm.intr.memset"(%d, %c, %n) <{arg_attrs = [{llvm.align = 2 : i64}, {}, {}], isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "set6_a2"
  // CHECK:      %[[C:.*]] = "riscv.li"() <{"value" = -6148914691236517206 : i64}>
  // CHECK-NEXT: "riscv.sh"(%[[C]], %[[D:.*]]) <{"value" = 0 : i64}>
  // CHECK-NEXT: "riscv.sh"(%[[C]], %[[D]]) <{"value" = 2 : i64}>
  // CHECK-NEXT: "riscv.sh"(%[[C]], %[[D]]) <{"value" = 4 : i64}>
  // CHECK-NEXT: "llvm.return"

  // Variable fill, wider than a byte: splat by multiplying with 0x0101010101010101.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, i8)>, linkage = #llvm.linkage<external>, sym_name = "set8_a8"}> ({
  ^bb0(%d: !llvm.ptr, %c: i8):
    %n = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    "llvm.intr.memset"(%d, %c, %n) <{arg_attrs = [{llvm.align = 8 : i64}, {}, {}], isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "set8_a8"
  // CHECK:      %[[E:.*]] = "riscv.zextb"(%{{.*}})
  // CHECK-NEXT: %[[O:.*]] = "riscv.li"() <{"value" = 72340172838076673 : i64}>
  // CHECK-NEXT: %[[M:.*]] = "riscv.mul"(%[[E]], %[[O]])
  // CHECK-NEXT: "riscv.sd"(%[[M]], %{{.*}}) <{"value" = 0 : i64}>
  // CHECK-NEXT: "llvm.return"

  // Variable fill, byte stores only: no splat needed.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, i8)>, linkage = #llvm.linkage<external>, sym_name = "set2"}> ({
  ^bb0(%d: !llvm.ptr, %c: i8):
    %n = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    "llvm.intr.memset"(%d, %c, %n) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "set2"
  // CHECK-NOT:  riscv.mul
  // CHECK:      "riscv.sb"(%[[C:.*]], %[[D:.*]]) <{"value" = 0 : i64}>
  // CHECK-NEXT: "riscv.sb"(%[[C]], %[[D]]) <{"value" = 1 : i64}>
  // CHECK-NEXT: "llvm.return"

  // 12 bytes, unknown alignment: a call, with the fill byte widened to an int.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, i8)>, linkage = #llvm.linkage<external>, sym_name = "set12"}> ({
  ^bb0(%d: !llvm.ptr, %c: i8):
    %n = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    "llvm.intr.memset"(%d, %c, %n) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "set12"
  // CHECK:      %[[E:.*]] = "riscv.zextb"(%{{.*}})
  // CHECK:      "riscv_cf.call"(%{{.*}}, %[[E]], %{{.*}}) <{"callee" = @memset}>
}) : () -> ()
