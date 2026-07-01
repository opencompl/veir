// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb(%a: i64):
        %ctlz = "llvm.intr.ctlz"(%a) <{is_zero_poison = false}> : (i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.clz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %ctlz_poison = "llvm.intr.ctlz"(%a) <{is_zero_poison = true}> : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.clz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %cttz = "llvm.intr.cttz"(%a) <{is_zero_poison = false}> : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.ctz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %cttz_poison = "llvm.intr.cttz"(%a) <{is_zero_poison = true}> : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.ctz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %ctpop = "llvm.intr.ctpop"(%a) : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.cpop"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %bswap = "llvm.intr.bswap"(%a) : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.rev8"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %bitreverse = "llvm.intr.bitreverse"(%a) : (i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{{.*}}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{{.*}}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{{.*}}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.rev8"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        "func.return"() : () -> ()
    }) : () -> ()
    "func.func"()  <{function_type = (i32) -> ()}> ({
    ^bb(%a: i32):
        %ctlz32 = "llvm.intr.ctlz"(%a) <{is_zero_poison = false}> : (i32) -> i32
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.clzw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        %cttz32 = "llvm.intr.cttz"(%a) <{is_zero_poison = false}> : (i32) -> i32
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.ctzw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        %ctpop32 = "llvm.intr.ctpop"(%a) : (i32) -> i32
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.cpopw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        %bswap32 = "llvm.intr.bswap"(%a) : (i32) -> i32
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.rev8"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        %bitreverse32 = "llvm.intr.bitreverse"(%a) : (i32) -> i32
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{{.*}}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{{.*}}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{{.*}}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.rev8"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
