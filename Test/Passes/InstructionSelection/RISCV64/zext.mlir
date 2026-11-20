// RUN: veir-opt %s -p=riscv | filecheck %s

// Zero extensions from `i1`, `i8`, `i16` and `i32` are selected.

"builtin.module"() ({
    "func.func"()  <{function_type = (i1, i16, i32, i42, i8) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i1, %b: i16, %c: i32, %d: i42, %e : i8):
        %sexta = "llvm.zext"(%b) : (i16) -> i64
        %sextb = "llvm.zext"(%b) : (i16) -> i32
        %sextc = "llvm.zext"(%c) : (i32) -> i64
        %sextd = "llvm.zext"(%a) : (i1) -> i64
        %zextd = "llvm.zext"(%e) : (i8) -> i32
        %zexte = "llvm.zext"(%a) : (i1) -> i32
        %zextf = "llvm.zext"(%a) : (i1) -> i16
        %zextg = "llvm.zext"(%a) : (i1) -> i8
          // CHECK:           func.func @foo([[A:.*]]: i1, [[B:.*]]: i16, [[C:.*]]: i32, [[D:.*]]: i42, [[E:.*]]: i8) {
          // CHECK-NEXT:      %[[F:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
          // CHECK-NEXT:      %[[G:.*]] = "riscv.zexth"(%[[F]]) : (!riscv.reg) -> !riscv.reg
          // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"(%[[G]]) : (!riscv.reg) -> i64
          // CHECK-NEXT:      %[[I:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
          // CHECK-NEXT:      %[[J:.*]] = "riscv.zexth"(%[[I]]) : (!riscv.reg) -> !riscv.reg
          // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"(%[[J]]) : (!riscv.reg) -> i32
          // CHECK-NEXT:      %[[L:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
          // CHECK-NEXT:      %[[M:.*]] = "riscv.zextw"(%[[L]]) : (!riscv.reg) -> !riscv.reg
          // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"(%[[M]]) : (!riscv.reg) -> i64
          // CHECK-NEXT:      %[[O:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i1) -> !riscv.reg
          // CHECK-NEXT:      %[[P:.*]] = "riscv.andi"(%[[O]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
          // CHECK-NEXT:      %[[Q:.*]] = "builtin.unrealized_conversion_cast"(%[[P]]) : (!riscv.reg) -> i64
          // CHECK-NEXT:      %[[R:.*]] = "builtin.unrealized_conversion_cast"([[E]]) : (i8) -> !riscv.reg
          // CHECK-NEXT:      %[[S:.*]] = "riscv.andi"(%[[R]]) <{"value" = 255 : i64}> : (!riscv.reg) -> !riscv.reg
          // CHECK-NEXT:      %[[T:.*]] = "builtin.unrealized_conversion_cast"(%[[S]]) : (!riscv.reg) -> i32
          // CHECK-NEXT:      %[[U:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i1) -> !riscv.reg
          // CHECK-NEXT:      %[[V:.*]] = "riscv.andi"(%[[U]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
          // CHECK-NEXT:      %[[W:.*]] = "builtin.unrealized_conversion_cast"(%[[V]]) : (!riscv.reg) -> i32
          // CHECK-NEXT:      %[[X:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i1) -> !riscv.reg
          // CHECK-NEXT:      %[[Y:.*]] = "riscv.andi"(%[[X]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
          // CHECK-NEXT:      %[[Z:.*]] = "builtin.unrealized_conversion_cast"(%[[Y]]) : (!riscv.reg) -> i16
          // CHECK-NEXT:      %[[AA:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i1) -> !riscv.reg
          // CHECK-NEXT:      %[[AB:.*]] = "riscv.andi"(%[[AA]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
          // CHECK-NEXT:      %[[AC:.*]] = "builtin.unrealized_conversion_cast"(%[[AB]]) : (!riscv.reg) -> i8
        "test.test"(%sexta) : (i64) -> ()
        "test.test"(%sextb) : (i32) -> ()
        "test.test"(%sextc) : (i64) -> ()
        "test.test"(%sextd) : (i64) -> ()
        "test.test"(%zextd) : (i32) -> ()
        "test.test"(%zexte) : (i32) -> ()
        "test.test"(%zextf) : (i16) -> ()
        "test.test"(%zextg) : (i8) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

