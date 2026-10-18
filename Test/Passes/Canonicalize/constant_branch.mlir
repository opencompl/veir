// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Branches whose constant operands select a single successor become
// unconditional branches to that successor, forwarding its operands.

"builtin.module"() ({

// CHECK-LABEL: func.func @cf_true
// CHECK: %[[A:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: "cf.br"(%[[A]]) [^[[TRUE:[0-9]+]]] : (i32) -> ()
// CHECK: ^[[TRUE]](%{{.*}} : i32):
"func.func"() <{sym_name = "cf_true", function_type = () -> i32}> ({
^entry:
  %a = "test.test"() : () -> i32
  %b = "test.test"() : () -> i32
  %condition = "arith.constant"() <{value = true}> : () -> i1
  "cf.cond_br"(%condition, %a, %b) [^true, ^false]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^true(%x : i32):
  "func.return"(%x) : (i32) -> ()
^false(%y : i32):
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK-LABEL: func.func @cf_false
// CHECK: %[[A:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: "cf.br"(%[[B]]) [^[[FALSE:[0-9]+]]] : (i32) -> ()
// CHECK: ^[[FALSE]](%{{.*}} : i32):
// CHECK-NEXT: "func.return"
"func.func"() <{sym_name = "cf_false", function_type = () -> i32}> ({
^entry:
  %a = "test.test"() : () -> i32
  %b = "test.test"() : () -> i32
  %condition = "arith.constant"() <{value = false}> : () -> i1
  "cf.cond_br"(%condition, %a, %b) [^true, ^false]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^true(%x : i32):
  "func.return"(%x) : (i32) -> ()
^false(%y : i32):
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// Both successors are the same block, so the successor is identified by its
// index and the false successor's operand is forwarded.
// CHECK-LABEL: func.func @cf_same_successor
// CHECK: %[[A:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: "cf.br"(%[[B]]) [^{{[0-9]+}}] : (i32) -> ()
"func.func"() <{sym_name = "cf_same_successor", function_type = () -> i32}> ({
^entry:
  %a = "test.test"() : () -> i32
  %b = "test.test"() : () -> i32
  %condition = "arith.constant"() <{value = false}> : () -> i1
  "cf.cond_br"(%condition, %a, %b) [^join, ^join]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^join(%x : i32):
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK-LABEL: func.func @llvm_true
// CHECK: %[[A:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: "llvm.br"(%[[A]]) [^[[TRUE:[0-9]+]]] : (i32) -> ()
// CHECK: ^[[TRUE]](%{{.*}} : i32):
"func.func"() <{sym_name = "llvm_true", function_type = () -> i32}> ({
^entry:
  %a = "test.test"() : () -> i32
  %b = "test.test"() : () -> i32
  %condition = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
  "llvm.cond_br"(%condition, %a, %b) [^true, ^false]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^true(%x : i32):
  "func.return"(%x) : (i32) -> ()
^false(%y : i32):
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK-LABEL: func.func @llvm_switch_case
// CHECK: %[[D:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: %[[A:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: "llvm.br"(%[[B]]) [^{{[0-9]+}}] : (i32) -> ()
"func.func"() <{sym_name = "llvm_switch_case", function_type = () -> i32}> ({
^entry:
  %d = "test.test"() : () -> i32
  %a = "test.test"() : () -> i32
  %b = "test.test"() : () -> i32
  %v = "llvm.mlir.constant"() <{value = 35 : i32}> : () -> i32
  "llvm.switch"(%v, %d, %a, %b) [^dflt, ^c0, ^c1]
    <{"case_operand_segments" = array<i32: 1, 1>, "case_values" = dense<[13, 35]> : vector<2xi32>,
      "operandSegmentSizes" = array<i32: 1, 1, 2>}> : (i32, i32, i32, i32) -> ()
^dflt(%x : i32):
  "func.return"(%x) : (i32) -> ()
^c0(%y : i32):
  "func.return"(%y) : (i32) -> ()
^c1(%z : i32):
  "func.return"(%z) : (i32) -> ()
}) : () -> ()

// CHECK-LABEL: func.func @llvm_switch_default
// CHECK: %[[D:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: %[[A:.*]] = "test.test"() : () -> i32
// CHECK-NEXT: "llvm.br"(%[[D]]) [^{{[0-9]+}}] : (i32) -> ()
"func.func"() <{sym_name = "llvm_switch_default", function_type = () -> i32}> ({
^entry:
  %d = "test.test"() : () -> i32
  %a = "test.test"() : () -> i32
  %v = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
  "llvm.switch"(%v, %d, %a) [^dflt, ^c0]
    <{"case_operand_segments" = array<i32: 1>, "case_values" = dense<[13]> : vector<1xi32>,
      "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i32, i32, i32) -> ()
^dflt(%x : i32):
  "func.return"(%x) : (i32) -> ()
^c0(%y : i32):
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// An unknown condition leaves the branch alone.
// CHECK-LABEL: func.func @unknown_condition
// CHECK: "cf.cond_br"
"func.func"() <{sym_name = "unknown_condition", function_type = () -> ()}> ({
^entry:
  %condition = "test.test"() : () -> i1
  "cf.cond_br"(%condition) [^true, ^false]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^true:
  "func.return"() : () -> ()
^false:
  "func.return"() : () -> ()
}) : () -> ()


// RISC-V conditional branches select their successor from constant registers.

// x == 0 branches to the first successor.
// CHECK-LABEL: func.func @riscv_beqz
// CHECK: %[[A:.*]] = "test.test"() : () -> !riscv.reg
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> !riscv.reg
// CHECK: "riscv_cf.branch"(%[[A]]) [^{{[0-9]+}}] : (!riscv.reg) -> ()
// CHECK-NOT: "riscv_cf.beqz"
"func.func"() <{sym_name = "riscv_beqz", function_type = () -> !riscv.reg}> ({
^entry:
  %a = "test.test"() : () -> !riscv.reg
  %b = "test.test"() : () -> !riscv.reg
  %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  %neg1 = "riscv.li"() <{value = -1 : i64}> : () -> !riscv.reg
  "riscv_cf.beqz"(%zero, %a, %b) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
^taken(%x : !riscv.reg):
  "func.return"(%x) : (!riscv.reg) -> ()
^fallthrough(%y : !riscv.reg):
  "func.return"(%y) : (!riscv.reg) -> ()
}) : () -> ()

// x != 0 branches to the second successor.
// CHECK-LABEL: func.func @riscv_bnez
// CHECK: %[[A:.*]] = "test.test"() : () -> !riscv.reg
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> !riscv.reg
// CHECK: "riscv_cf.branch"(%[[B]]) [^{{[0-9]+}}] : (!riscv.reg) -> ()
// CHECK-NOT: "riscv_cf.bnez"
"func.func"() <{sym_name = "riscv_bnez", function_type = () -> !riscv.reg}> ({
^entry:
  %a = "test.test"() : () -> !riscv.reg
  %b = "test.test"() : () -> !riscv.reg
  %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  %neg1 = "riscv.li"() <{value = -1 : i64}> : () -> !riscv.reg
  "riscv_cf.bnez"(%zero, %a, %b) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
^taken(%x : !riscv.reg):
  "func.return"(%x) : (!riscv.reg) -> ()
^fallthrough(%y : !riscv.reg):
  "func.return"(%y) : (!riscv.reg) -> ()
}) : () -> ()

// -1 == 1 branches to the second successor.
// CHECK-LABEL: func.func @riscv_beq
// CHECK: %[[A:.*]] = "test.test"() : () -> !riscv.reg
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> !riscv.reg
// CHECK: "riscv_cf.branch"(%[[B]]) [^{{[0-9]+}}] : (!riscv.reg) -> ()
// CHECK-NOT: "riscv_cf.beq"
"func.func"() <{sym_name = "riscv_beq", function_type = () -> !riscv.reg}> ({
^entry:
  %a = "test.test"() : () -> !riscv.reg
  %b = "test.test"() : () -> !riscv.reg
  %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  %neg1 = "riscv.li"() <{value = -1 : i64}> : () -> !riscv.reg
  "riscv_cf.beq"(%neg1, %one, %a, %b) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
^taken(%x : !riscv.reg):
  "func.return"(%x) : (!riscv.reg) -> ()
^fallthrough(%y : !riscv.reg):
  "func.return"(%y) : (!riscv.reg) -> ()
}) : () -> ()

// -1 != 1 branches to the first successor.
// CHECK-LABEL: func.func @riscv_bne
// CHECK: %[[A:.*]] = "test.test"() : () -> !riscv.reg
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> !riscv.reg
// CHECK: "riscv_cf.branch"(%[[A]]) [^{{[0-9]+}}] : (!riscv.reg) -> ()
// CHECK-NOT: "riscv_cf.bne"
"func.func"() <{sym_name = "riscv_bne", function_type = () -> !riscv.reg}> ({
^entry:
  %a = "test.test"() : () -> !riscv.reg
  %b = "test.test"() : () -> !riscv.reg
  %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  %neg1 = "riscv.li"() <{value = -1 : i64}> : () -> !riscv.reg
  "riscv_cf.bne"(%neg1, %one, %a, %b) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
^taken(%x : !riscv.reg):
  "func.return"(%x) : (!riscv.reg) -> ()
^fallthrough(%y : !riscv.reg):
  "func.return"(%y) : (!riscv.reg) -> ()
}) : () -> ()

// -1 <s 1 branches to the first successor.
// CHECK-LABEL: func.func @riscv_blt
// CHECK: %[[A:.*]] = "test.test"() : () -> !riscv.reg
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> !riscv.reg
// CHECK: "riscv_cf.branch"(%[[A]]) [^{{[0-9]+}}] : (!riscv.reg) -> ()
// CHECK-NOT: "riscv_cf.blt"
"func.func"() <{sym_name = "riscv_blt", function_type = () -> !riscv.reg}> ({
^entry:
  %a = "test.test"() : () -> !riscv.reg
  %b = "test.test"() : () -> !riscv.reg
  %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  %neg1 = "riscv.li"() <{value = -1 : i64}> : () -> !riscv.reg
  "riscv_cf.blt"(%neg1, %one, %a, %b) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
^taken(%x : !riscv.reg):
  "func.return"(%x) : (!riscv.reg) -> ()
^fallthrough(%y : !riscv.reg):
  "func.return"(%y) : (!riscv.reg) -> ()
}) : () -> ()

// -1 >=s 1 branches to the second successor.
// CHECK-LABEL: func.func @riscv_bge
// CHECK: %[[A:.*]] = "test.test"() : () -> !riscv.reg
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> !riscv.reg
// CHECK: "riscv_cf.branch"(%[[B]]) [^{{[0-9]+}}] : (!riscv.reg) -> ()
// CHECK-NOT: "riscv_cf.bge"
"func.func"() <{sym_name = "riscv_bge", function_type = () -> !riscv.reg}> ({
^entry:
  %a = "test.test"() : () -> !riscv.reg
  %b = "test.test"() : () -> !riscv.reg
  %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  %neg1 = "riscv.li"() <{value = -1 : i64}> : () -> !riscv.reg
  "riscv_cf.bge"(%neg1, %one, %a, %b) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
^taken(%x : !riscv.reg):
  "func.return"(%x) : (!riscv.reg) -> ()
^fallthrough(%y : !riscv.reg):
  "func.return"(%y) : (!riscv.reg) -> ()
}) : () -> ()

// -1 <u 1 branches to the second successor.
// CHECK-LABEL: func.func @riscv_bltu
// CHECK: %[[A:.*]] = "test.test"() : () -> !riscv.reg
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> !riscv.reg
// CHECK: "riscv_cf.branch"(%[[B]]) [^{{[0-9]+}}] : (!riscv.reg) -> ()
// CHECK-NOT: "riscv_cf.bltu"
"func.func"() <{sym_name = "riscv_bltu", function_type = () -> !riscv.reg}> ({
^entry:
  %a = "test.test"() : () -> !riscv.reg
  %b = "test.test"() : () -> !riscv.reg
  %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  %neg1 = "riscv.li"() <{value = -1 : i64}> : () -> !riscv.reg
  "riscv_cf.bltu"(%neg1, %one, %a, %b) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
^taken(%x : !riscv.reg):
  "func.return"(%x) : (!riscv.reg) -> ()
^fallthrough(%y : !riscv.reg):
  "func.return"(%y) : (!riscv.reg) -> ()
}) : () -> ()

// -1 >=u 1 branches to the first successor.
// CHECK-LABEL: func.func @riscv_bgeu
// CHECK: %[[A:.*]] = "test.test"() : () -> !riscv.reg
// CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> !riscv.reg
// CHECK: "riscv_cf.branch"(%[[A]]) [^{{[0-9]+}}] : (!riscv.reg) -> ()
// CHECK-NOT: "riscv_cf.bgeu"
"func.func"() <{sym_name = "riscv_bgeu", function_type = () -> !riscv.reg}> ({
^entry:
  %a = "test.test"() : () -> !riscv.reg
  %b = "test.test"() : () -> !riscv.reg
  %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  %neg1 = "riscv.li"() <{value = -1 : i64}> : () -> !riscv.reg
  "riscv_cf.bgeu"(%neg1, %one, %a, %b) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
^taken(%x : !riscv.reg):
  "func.return"(%x) : (!riscv.reg) -> ()
^fallthrough(%y : !riscv.reg):
  "func.return"(%y) : (!riscv.reg) -> ()
}) : () -> ()

// A register that is not a known constant leaves the branch alone.
// CHECK-LABEL: func.func @riscv_unknown
// CHECK: "riscv_cf.blt"
"func.func"() <{sym_name = "riscv_unknown", function_type = () -> ()}> ({
^entry:
  %x = "test.test"() : () -> !riscv.reg
  %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  "riscv_cf.blt"(%x, %one) [^taken, ^fallthrough]
    <{operandSegmentSizes = array<i32: 1, 1, 0, 0>}> : (!riscv.reg, !riscv.reg) -> ()
^taken:
  "func.return"() : () -> ()
^fallthrough:
  "func.return"() : () -> ()
}) : () -> ()
}) : () -> ()
