// RUN: veir-opt %s -p=riscv | filecheck %s

// The saturating intrinsics go through gMIR. As in LLVM's GlobalISel with Zbb, the `i64` add and
// sub are lowered with min and max, and the shifts compare the shifted-back value to the operand.
// The `g_select`s become Zicond selects.

"builtin.module"() ({

    // sadd.sat(x, y) = x + smin(smax(INT_MIN - smin(x, 0), y), INT_MAX - smax(x, 0))
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f0"}> ({
    ^bb0(%x: i64, %y: i64):
        // CHECK-LABEL: func.func @f0
        %r = "llvm.intr.sadd.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.li"() <{"value" = 9223372036854775807 : i64}>
        // CHECK:      "riscv.li"() <{"value" = -9223372036854775808 : i64}>
        // CHECK:      "riscv.max"
        // CHECK:      "riscv.sub"
        // CHECK:      "riscv.min"
        // CHECK:      "riscv.sub"
        // CHECK:      "riscv.max"
        // CHECK:      "riscv.min"
        // CHECK:      "riscv.add"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // ssub.sat(x, y) = x - smin(smax(smax(x, -1) - INT_MAX, y), smin(x, -1) - INT_MIN)
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f1"}> ({
    ^bb0(%x: i64, %y: i64):
        // CHECK-LABEL: func.func @f1
        %r = "llvm.intr.ssub.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.li"() <{"value" = -1 : i64}>
        // CHECK:      "riscv.max"
        // CHECK:      "riscv.add"
        // CHECK:      "riscv.min"
        // CHECK:      "riscv.add"
        // CHECK:      "riscv.max"
        // CHECK:      "riscv.min"
        // CHECK:      "riscv.sub"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // uadd.sat(x, y) = x + umin(~x, y)
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f2"}> ({
    ^bb0(%x: i64, %y: i64):
        // CHECK-LABEL: func.func @f2
        %r = "llvm.intr.uadd.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.xori"({{.*}}) <{"value" = -1 : i64}>
        // CHECK:      "riscv.minu"
        // CHECK:      "riscv.add"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // usub.sat(x, y) = x - umin(x, y)
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f3"}> ({
    ^bb0(%x: i64, %y: i64):
        // CHECK-LABEL: func.func @f3
        %r = "llvm.intr.usub.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.minu"
        // CHECK:      "riscv.sub"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // sshl.sat(x, y) = x != (x << y) >>s y ? (x <s 0 ? INT_MIN : INT_MAX) : x << y
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f4"}> ({
    ^bb0(%x: i64, %y: i64):
        // CHECK-LABEL: func.func @f4
        %r = "llvm.intr.sshl.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.sll"
        // CHECK:      "riscv.sra"
        // CHECK:      "riscv.li"() <{"value" = -9223372036854775808 : i64}>
        // CHECK:      "riscv.li"() <{"value" = 9223372036854775807 : i64}>
        // CHECK:      "riscv.slti"
        // CHECK:      "riscv.czeroeqz"
        // CHECK:      "riscv.czeronez"
        // CHECK:      "riscv.or"
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.sltu"
        // CHECK:      "riscv.czeroeqz"
        // CHECK:      "riscv.czeronez"
        // CHECK:      "riscv.or"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // ushl.sat(x, y) = x != (x << y) >>u y ? -1 : x << y
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f5"}> ({
    ^bb0(%x: i64, %y: i64):
        // CHECK-LABEL: func.func @f5
        %r = "llvm.intr.ushl.sat"(%x, %y) : (i64, i64) -> i64
        // CHECK:      "riscv.sll"
        // CHECK:      "riscv.srl"
        // CHECK:      "riscv.li"() <{"value" = -1 : i64}>
        // CHECK:      "riscv.xor"
        // CHECK:      "riscv.sltu"
        // CHECK:      "riscv.czeroeqz"
        // CHECK:      "riscv.czeronez"
        // CHECK:      "riscv.or"
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
