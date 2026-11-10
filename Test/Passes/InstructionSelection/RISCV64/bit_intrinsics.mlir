// RUN: veir-opt %s -p=riscv | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64) -> (), sym_name = "foo"}> ({
    ^bb(%a: i64):
        %ctlz = "llvm.intr.ctlz"(%a) <{is_zero_poison = false}> : (i64) -> i64
        // CHECK:      %[[A:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.clz"(%[[A]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %[[CTLZ:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        // The flag is dropped when selecting, so `cse` merges it with `%ctlz`.
        %ctlz_poison = "llvm.intr.ctlz"(%a) <{is_zero_poison = true}> : (i64) -> i64
        %cttz = "llvm.intr.cttz"(%a) <{is_zero_poison = false}> : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "riscv.ctz"(%[[A]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %[[CTTZ:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        // The flag is dropped when selecting, so `cse` merges it with `%cttz`.
        %cttz_poison = "llvm.intr.cttz"(%a) <{is_zero_poison = true}> : (i64) -> i64
        %ctpop = "llvm.intr.ctpop"(%a) : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "riscv.cpop"(%[[A]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %bswap = "llvm.intr.bswap"(%a) : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "riscv.rev8"(%[[A]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %bitreverse = "llvm.intr.bitreverse"(%a) : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "riscv.brev8"(%[[A]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.rev8"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        // CHECK-NEXT: "test.test"
        // CHECK-NEXT: "test.test"
        // CHECK-NEXT: "test.test"
        // CHECK-NEXT: "test.test"(%[[CTLZ]]) : (i64) -> ()
        // CHECK-NEXT: "test.test"(%[[CTLZ]]) : (i64) -> ()
        // CHECK-NEXT: "test.test"(%[[CTTZ]]) : (i64) -> ()
        // CHECK-NEXT: "test.test"(%[[CTTZ]]) : (i64) -> ()
        "test.test"(%ctpop) : (i64) -> ()
        "test.test"(%bswap) : (i64) -> ()
        "test.test"(%bitreverse) : (i64) -> ()
        "test.test"(%ctlz) : (i64) -> ()
        "test.test"(%ctlz_poison) : (i64) -> ()
        "test.test"(%cttz) : (i64) -> ()
        "test.test"(%cttz_poison) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    "func.func"()  <{function_type = (i32) -> (), sym_name = "bar"}> ({
    ^bb(%a: i32):
        %ctlz32 = "llvm.intr.ctlz"(%a) <{is_zero_poison = false}> : (i32) -> i32
        // CHECK:      %[[B:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.clzw"(%[[B]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        %cttz32 = "llvm.intr.cttz"(%a) <{is_zero_poison = false}> : (i32) -> i32
        // CHECK-NEXT: %{{.*}} = "riscv.ctzw"(%[[B]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        %ctpop32 = "llvm.intr.ctpop"(%a) : (i32) -> i32
        // CHECK-NEXT: %{{.*}} = "riscv.cpopw"(%[[B]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        %bswap32 = "llvm.intr.bswap"(%a) : (i32) -> i32
        // CHECK-NEXT: %{{.*}} = "riscv.rev8"(%[[B]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 32 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        %bitreverse32 = "llvm.intr.bitreverse"(%a) : (i32) -> i32
        // CHECK-NEXT: %{{.*}} = "riscv.brev8"(%[[B]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.rev8"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 32 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        "test.test"(%ctpop32) : (i32) -> ()
        "test.test"(%bswap32) : (i32) -> ()
        "test.test"(%bitreverse32) : (i32) -> ()
        "test.test"(%ctlz32) : (i32) -> ()
        "test.test"(%cttz32) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
