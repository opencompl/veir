// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,isel-riscv64,reconcile-cast | filecheck %s

// Peephole: comparing against a constant 0 on the rhs lowers `eq`/`ne` directly
// on the non-zero operand, with no `riscv.xor`. Canonicalization runs before
// isel and moves the constant to the rhs, so only the rhs case is handled.
//   a == 0  ->  riscv.sltiu a 1   (seqz)
//   a != 0  ->  riscv.sltu  0 a   (snez)

"builtin.module"() ({
    // eq, zero on the right: a == 0
    "func.func"() <{function_type = (i64) -> (i1), sym_name = "foo"}> ({
    ^bb0(%a: i64):
        %z = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %z) <{predicate = 0 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: func.func @foo(%{{.*}}: i64) -> i1 {
        // CHECK: "riscv.sltiu"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.xor"
    }) : () -> ()

    // ne, zero on the right: a != 0  ->  riscv.sltu 0 a (no xor)
    "func.func"() <{function_type = (i64) -> (i1), sym_name = "bar"}> ({
    ^bb0(%a: i64):
        %z = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
        %r = "llvm.icmp"(%a, %z) <{predicate = 1 : i64}> : (i64, i64) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: func.func @bar(%{{.*}}: i64) -> i1 {
        // CHECK: "riscv.sltu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.xor"
    }) : () -> ()

    // eq at i32: legalization creates a fresh `0`, which the peephole must see before
    // `gmirConstant` selects it into a register.
    "func.func"() <{function_type = (i32) -> (i1), sym_name = "baz"}> ({
    ^bb0(%a: i32):
        %z = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
        %r = "llvm.icmp"(%a, %z) <{predicate = 0 : i64}> : (i32, i32) -> i1
        "func.return"(%r) : (i1) -> ()
        // CHECK-LABEL: func.func @baz(%{{.*}}: i32) -> i1 {
        // CHECK-NOT: "riscv.xor"
        // CHECK: "riscv.sltiu"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    }) : () -> ()
}) : () -> ()
