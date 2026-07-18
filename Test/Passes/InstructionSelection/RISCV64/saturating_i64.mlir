// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({

    // llvm.intr.sadd.sat.i64 -> LLVM RV64+Zicond signed saturating-add sequence
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f0"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.sadd.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.add"
        // CHECK:      "riscv.srli"({{.*}}) <{"value" = 63 : i64}>
        // CHECK:      "riscv.slt"
        // CHECK:      "riscv.srai"({{.*}}) <{"value" = 63 : i64}>
        // CHECK:      "riscv.slli"({{.*}}) <{"value" = 63 : i64}>
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.czeronez"
        // CHECK:      "riscv.czeroeqz"
        // CHECK:      "riscv.or"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.ssub.sat.i64 -> LLVM RV64+Zicond signed saturating-sub sequence
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f1"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.ssub.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.sub"
        // CHECK:      "riscv.slt"
        // CHECK:      "riscv.srli"({{.*}}) <{"value" = 63 : i64}>
        // CHECK:      "riscv.srai"({{.*}}) <{"value" = 63 : i64}>
        // CHECK:      "riscv.slli"({{.*}}) <{"value" = 63 : i64}>
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.czeronez"
        // CHECK:      "riscv.czeroeqz"
        // CHECK:      "riscv.or"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.uadd.sat.i64 -> not y; minu x, not-y; add
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f2"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.uadd.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.xori"({{.*}}) <{"value" = -1 : i64}>
        // CHECK:      "riscv.minu"
        // CHECK:      "riscv.add"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.usub.sat.i64 -> maxu x, y; sub y
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f3"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.usub.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.maxu"
        // CHECK:      "riscv.sub"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.sshl.sat.i64 -> LLVM RV64+Zicond signed saturating-shl sequence
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f4"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.sshl.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.sll"
        // CHECK:      "riscv.sra"
        // CHECK:      "riscv.srai"({{.*}}) <{"value" = 63 : i64}>
        // CHECK:      "riscv.srli"({{.*}}) <{"value" = 1 : i64}>
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.czeronez"
        // CHECK:      "riscv.czeroeqz"
        // CHECK:      "riscv.or"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.ushl.sat.i64 -> LLVM RV64 unsigned saturating-shl sequence
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f5"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.ushl.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.sll"
        // CHECK:      "riscv.srl"
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.sltiu"({{.*}}) <{"value" = 1 : i64}>
        // CHECK:      "riscv.addi"({{.*}}) <{"value" = -1 : i64}>
        // CHECK:      "riscv.or"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
