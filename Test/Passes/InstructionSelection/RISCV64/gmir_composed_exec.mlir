// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64,postlegalizer-combiner-riscv64,isel-br-riscv64,isel-riscv64,isel-abi-riscv64,reconcile-cast,riscv-combine,dce > %t
// RUN: veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=SEL < %t

// The composed and immediate selections that `isel-riscv64` took over from
// `isel-sdag-riscv64`, on legalized gMIR: `andn`/`orn`/`xnor` with the `not` on either side,
// `orcb`, `bexti`, `slliuw`, the Zbs single-bit immediates, and `slti`/`sltiu` at the
// immediate boundaries (including `ule` against `-1`, which must not use `sltiu`).

// SEL-DAG: "riscv.andn"
// SEL-DAG: "riscv.orn"
// SEL-DAG: "riscv.xnor"
// SEL-DAG: "riscv.orcb"
// SEL-DAG: "riscv.bexti"(%{{.*}}) <{"value" = 40 : i64}>
// SEL-DAG: "riscv.slliuw"(%{{.*}}) <{"value" = 5 : i64}>
// SEL-DAG: "riscv.bseti"(%{{.*}}) <{"value" = 12 : i64}>
// SEL-DAG: "riscv.binvi"(%{{.*}}) <{"value" = 12 : i64}>
// SEL-DAG: "riscv.bclri"(%{{.*}}) <{"value" = 40 : i64}>
// `sle x, 2047` needs the immediate 2048, and `ule x, -1` would wrap, so both use the
// register-register comparison. `ule x, -2049` uses the immediate -2048.
// SEL-DAG: "riscv.slt"(%{{.*}}, %{{.*}})
// SEL-DAG: "riscv.sltu"(%{{.*}}, %{{.*}})
// SEL-DAG: "riscv.sltiu"(%{{.*}}) <{"value" = -2048 : i64}>
// SEL-DAG: "riscv.slti"(%{{.*}}) <{"value" = 5 : i64}>
// SEL-DAG: "riscv.sltiu"(%{{.*}}) <{"value" = 5 : i64}>
// SEL-NOT: "riscv.slti"(%{{.*}}) <{"value" = 2048 : i64}>

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)}> ({
    // `llvm.freeze` hides the inputs from the constant folds of the post-legalizer combiner.
    %x0 = "llvm.mlir.constant"() <{value = 81985529216486895 : i64}> : () -> i64
    %y0 = "llvm.mlir.constant"() <{value = -6148914691236517206 : i64}> : () -> i64
    %x = "llvm.freeze"(%x0) : (i64) -> i64
    %y = "llvm.freeze"(%y0) : (i64) -> i64
    %m1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %ny = "llvm.xor"(%y, %m1) : (i64, i64) -> i64
    %r0 = "llvm.and"(%ny, %x) : (i64, i64) -> i64
    %r1 = "llvm.or"(%x, %ny) : (i64, i64) -> i64
    %r2 = "llvm.xor"(%ny, %x) : (i64, i64) -> i64
    %mask = "llvm.mlir.constant"() <{value = 578721382704613384 : i64}> : () -> i64
    %mm = "llvm.and"(%x, %mask) : (i64, i64) -> i64
    %c5 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %c3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %sh = "llvm.shl"(%mm, %c5) : (i64, i64) -> i64
    %sr = "llvm.lshr"(%mm, %c3) : (i64, i64) -> i64
    %r3 = "llvm.sub"(%sh, %sr) : (i64, i64) -> i64
    %c40 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %e = "llvm.lshr"(%x, %c40) : (i64, i64) -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r4 = "llvm.and"(%e, %one) : (i64, i64) -> i64
    %t = "llvm.trunc"(%y) : (i64) -> i32
    %z = "llvm.zext"(%t) : (i32) -> i64
    %r5 = "llvm.shl"(%z, %c5) : (i64, i64) -> i64
    %bit = "llvm.mlir.constant"() <{value = 4096 : i64}> : () -> i64
    %r6 = "llvm.or"(%x, %bit) : (i64, i64) -> i64
    %r7 = "llvm.xor"(%x, %bit) : (i64, i64) -> i64
    %nbit = "llvm.mlir.constant"() <{value = -1099511627777 : i64}> : () -> i64
    %r8 = "llvm.and"(%x, %nbit) : (i64, i64) -> i64
    %k = "llvm.mlir.constant"() <{value = 2047 : i64}> : () -> i64
    %km = "llvm.mlir.constant"() <{value = -2049 : i64}> : () -> i64
    %v0 = "llvm.mlir.constant"() <{value = 2047 : i64}> : () -> i64
    %v = "llvm.freeze"(%v0) : (i64) -> i64
    %m1f = "llvm.freeze"(%m1) : (i64) -> i64
    %q0 = "llvm.icmp"(%v, %k) <{predicate = 3 : i64}> : (i64, i64) -> i1
    %r9 = "llvm.zext"(%q0) : (i1) -> i64
    %q1 = "llvm.icmp"(%m1f, %km) <{predicate = 7 : i64}> : (i64, i64) -> i1
    %r10 = "llvm.zext"(%q1) : (i1) -> i64
    %q2 = "llvm.icmp"(%m1f, %m1) <{predicate = 7 : i64}> : (i64, i64) -> i1
    %r11 = "llvm.zext"(%q2) : (i1) -> i64
    %q3 = "llvm.icmp"(%y, %c5) <{predicate = 5 : i64}> : (i64, i64) -> i1
    %r12 = "llvm.zext"(%q3) : (i1) -> i64
    %q4 = "llvm.icmp"(%y, %c5) <{predicate = 9 : i64}> : (i64, i64) -> i1
    %r13 = "llvm.zext"(%q4) : (i1) -> i64
    %q5 = "llvm.icmp"(%y, %c5) <{predicate = 2 : i64}> : (i64, i64) -> i1
    %r14 = "llvm.zext"(%q5) : (i1) -> i64
    %q6 = "llvm.icmp"(%y, %c5) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %r15 = "llvm.zext"(%q6) : (i1) -> i64
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5, %r6, %r7, %r8, %r9, %r10, %r11, %r12, %r13, %r14, %r15) : (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0101454501014545#64, 0x55775577ddffddff#64, 0x54761032dcfe98ba#64, 0x00000000ffffffff#64, 0x0000000000000001#64, 0x0000001555555540#64, 0x0123456789abddef#64, 0x0123456789abddef#64, 0x0123446789abcdef#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000001#64, 0x0000000000000000#64]
