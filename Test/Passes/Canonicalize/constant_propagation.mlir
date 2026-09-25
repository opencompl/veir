// RUN: veir-opt %s -p=canonicalize | filecheck %s
// RUN: veir-opt %s -p='canonicalize{sccp=false}' | filecheck %s --check-prefix=NO-SCCP

"builtin.module"() ({
  // Propagate zero through a block argument, then fold a chain to a
  // nonconstant operand. The extended add has both kinds of fold result.
  "func.func"() <{sym_name = "operand_folds", function_type = (i32) -> (i32, i1)}> ({
  ^entry(%x : i32):
    // CHECK: func.func @operand_folds(%[[X:.*]]: i32)
    // NO-SCCP-LABEL: func.func @operand_folds
    %zero = "arith.constant"() <{value = 0 : i32}> : () -> i32
    "cf.br"(%zero) [^body] : (i32) -> ()
  ^body(%forwarded : i32):
    // CHECK: ^{{[0-9]+}}(%{{.*}} : i32):
    // CHECK-NEXT: %[[FALSE:.*]] = "arith.constant"() <{"value" = false}> : () -> i1
    // CHECK-NEXT: "func.return"(%[[X]], %[[FALSE]]) : (i32, i1) -> ()
    // NO-SCCP: "arith.addi"
    // NO-SCCP: "arith.addi"
    // NO-SCCP: "arith.addui_extended"
    %a = "arith.addi"(%forwarded, %x) : (i32, i32) -> i32
    %b = "arith.addi"(%a, %forwarded) : (i32, i32) -> i32
    %sum, %overflow = "arith.addui_extended"(%b, %forwarded) : (i32, i32) -> (i32, i1)
    "func.return"(%sum, %overflow) : (i32, i1) -> ()
  }) : () -> ()

  // Equal incoming constants survive a join; conflicting constants do not.
  // The argument retains its LLVM materializer, while the sum uses Arith's.
  "func.func"() <{sym_name = "join_and_dialect", function_type = (i1) -> (i32, i32, i32)}> ({
  ^entry(%condition : i1):
    // CHECK-LABEL: func.func @join_and_dialect
    %left = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %right = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %seven = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "cf.cond_br"(%condition, %left, %left, %right, %seven) [^join, ^join]
      <{operandSegmentSizes = array<i32: 1, 2, 2>}> : (i1, i32, i32, i32, i32) -> ()
  ^join(%same : i32, %different : i32):
    // CHECK: ^{{[0-9]+}}(%{{.*}} : i32, %[[DIFFERENT:.*]] : i32):
    // CHECK-NEXT: %[[FIVE:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
    // CHECK-NEXT: %[[TEN:.*]] = "arith.constant"() <{"value" = 10 : i32}> : () -> i32
    // CHECK-NEXT: "func.return"(%[[FIVE]], %[[DIFFERENT]], %[[TEN]]) : (i32, i32, i32) -> ()
    %sum = "arith.addi"(%same, %same) : (i32, i32) -> i32
    "func.return"(%same, %different, %sum) : (i32, i32, i32) -> ()
  }) : () -> ()

}) : () -> ()
