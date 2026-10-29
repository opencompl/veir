// RUN: veir-opt %s -p=riscv | filecheck %s

// The saturating intrinsics go through gMIR. As in LLVM's GlobalISel with Zbb, the `i64` add and
// sub are lowered with min and max, and the shifts compare the shifted-back value to the operand.

"builtin.module"() ({

    // sadd.sat(x, y) = x + smin(smax(INT_MIN - smin(x, 0), y), INT_MAX - smax(x, 0))
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f0"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.sadd.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f0
        // CHECK:      %[[MAX:.*]] = "riscv.li"() <{"value" = 9223372036854775807 : i64}>
        // CHECK:      %[[MIN:.*]] = "riscv.li"() <{"value" = -9223372036854775808 : i64}>
        // CHECK:      %[[SMAX:.*]] = "riscv.max"
        // CHECK:      %[[HI:.*]] = "riscv.sub"(%[[MAX]], %[[SMAX]])
        // CHECK:      %[[SMIN:.*]] = "riscv.min"
        // CHECK:      %[[LO:.*]] = "riscv.sub"(%[[MIN]], %[[SMIN]])
        // CHECK:      %[[CLAMP:.*]] = "riscv.max"(%[[LO]], %{{.*}})
        // CHECK:      %[[CLAMPED:.*]] = "riscv.min"(%[[CLAMP]], %[[HI]])
        // CHECK:      "riscv.add"(%{{.*}}, %[[CLAMPED]])
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // ssub.sat(x, y) = x - smin(smax(smax(x, -1) - INT_MAX, y), smin(x, -1) - INT_MIN)
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f1"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.ssub.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f1
        // CHECK:      %[[NEGONE:.*]] = "riscv.li"() <{"value" = -1 : i64}>
        // CHECK:      %[[SMAX:.*]] = "riscv.max"(%{{.*}}, %[[NEGONE]])
        // CHECK:      %[[LO:.*]] = "riscv.add"(%[[SMAX]], %{{.*}})
        // CHECK:      %[[SMIN:.*]] = "riscv.min"(%{{.*}}, %[[NEGONE]])
        // CHECK:      %[[HI:.*]] = "riscv.add"(%[[SMIN]], %{{.*}})
        // CHECK:      %[[CLAMP:.*]] = "riscv.max"(%[[LO]], %{{.*}})
        // CHECK:      %[[CLAMPED:.*]] = "riscv.min"(%[[CLAMP]], %[[HI]])
        // CHECK:      "riscv.sub"(%{{.*}}, %[[CLAMPED]])
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // uadd.sat(x, y) = x + umin(~x, y)
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f2"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.uadd.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f2
        // CHECK:      %[[NOT:.*]] = "riscv.xori"(%{{.*}}) <{"value" = -1 : i64}>
        // CHECK:      %[[MIN:.*]] = "riscv.minu"(%[[NOT]], %{{.*}})
        // CHECK:      "riscv.add"(%{{.*}}, %[[MIN]])
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // usub.sat(x, y) = x - umin(x, y)
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f3"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.usub.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f3
        // CHECK:      %[[MIN:.*]] = "riscv.minu"
        // CHECK:      "riscv.sub"(%{{.*}}, %[[MIN]])
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // sshl.sat(x, y) = x != (x << y) >>s y ? (x < 0 ? INT_MIN : INT_MAX) : x << y
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f4"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.sshl.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f4
        // CHECK:      %[[SHL:.*]] = "riscv.sll"
        // CHECK:      %[[BACK:.*]] = "riscv.sra"(%[[SHL]], %{{.*}})
        // CHECK:      %[[MIN:.*]] = "riscv.li"() <{"value" = -9223372036854775808 : i64}>
        // CHECK:      %[[MAX:.*]] = "riscv.li"() <{"value" = 9223372036854775807 : i64}>
        // CHECK:      %[[NEG:.*]] = "riscv.slt"
        // CHECK:      %[[T:.*]] = "riscv.czeroeqz"(%[[MIN]], %[[NEG]])
        // CHECK:      %[[F:.*]] = "riscv.czeronez"(%[[MAX]], %[[NEG]])
        // CHECK:      %[[SAT:.*]] = "riscv.or"(%[[T]], %[[F]])
        // CHECK:      %[[DIFF:.*]] = "riscv.xor"(%[[BACK]], %{{.*}})
        // CHECK:      %[[OV:.*]] = "riscv.sltu"(%{{.*}}, %[[DIFF]])
        // CHECK:      %[[T:.*]] = "riscv.czeroeqz"(%[[SAT]], %[[OV]])
        // CHECK:      %[[F:.*]] = "riscv.czeronez"(%[[SHL]], %[[OV]])
        // CHECK:      "riscv.or"(%[[T]], %[[F]])
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // ushl.sat(x, y) = x != (x << y) >>u y ? -1 : x << y
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f5"}> ({
    ^bb0(%x: i64, %y: i64):
        %r = "llvm.intr.ushl.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f5
        // CHECK:      %[[SHL:.*]] = "riscv.sll"
        // CHECK:      %[[BACK:.*]] = "riscv.srl"(%[[SHL]], %{{.*}})
        // CHECK:      %[[ALLONES:.*]] = "riscv.li"() <{"value" = -1 : i64}>
        // CHECK:      %[[DIFF:.*]] = "riscv.xor"(%[[BACK]], %{{.*}})
        // CHECK:      %[[OV:.*]] = "riscv.sltu"(%{{.*}}, %[[DIFF]])
        // CHECK:      %[[T:.*]] = "riscv.czeroeqz"(%[[ALLONES]], %[[OV]])
        // CHECK:      %[[F:.*]] = "riscv.czeronez"(%[[SHL]], %[[OV]])
        // CHECK:      "riscv.or"(%[[T]], %[[F]])
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
