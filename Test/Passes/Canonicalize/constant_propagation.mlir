// RUN: veir-opt %s -p=canonicalize | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "chain"}> ({
  ^entry:
    %two = "arith.constant"() <{value = 2 : i32}> : () -> i32
    %five = "arith.constant"() <{value = 5 : i32}> : () -> i32
    "cf.br"(%five) [^middle] : (i32) -> ()
  ^middle(%input : i32):
    %product = "arith.muli"(%input, %two) : (i32, i32) -> i32
    "cf.br"(%product) [^exit] : (i32) -> ()
  ^exit(%result : i32):
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @chain
  // CHECK: "cf.br"
  // CHECK: ^{{.*}}(%{{.*}}: i32):
  // CHECK-NEXT: %[[PRODUCT:.*]] = "arith.constant"() <{"value" = 10 : i32}>
  // CHECK-NEXT: "cf.br"(%[[PRODUCT]])
  // CHECK-NEXT: ^{{.*}}(%{{.*}}: i32):
  // CHECK-NEXT: %[[RESULT:.*]] = "arith.constant"() <{"value" = 10 : i32}>
  // CHECK-NEXT: "func.return"(%[[RESULT]])

  // Both successor edges target the same block, with distinct equal constants.
  // The materializer follows the dialect of a value a predecessor forwards in;
  // when the predecessors disagree the choice between them is arbitrary.
  "func.func"() <{function_type = (i1) -> i32, sym_name = "equal_join"}> ({
  ^entry(%cond : i1):
    %left = "arith.constant"() <{value = 42 : i32}> : () -> i32
    %right = "llvm.mlir.constant"() <{value = 42 : i32}> : () -> i32
    "cf.cond_br"(%cond, %left, %right) [^join, ^join]
      <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^join(%value : i32):
    "func.return"(%value) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @equal_join
  // CHECK: "cf.cond_br"
  // CHECK-NEXT: ^{{.*}}(%{{.*}}: i32):
  // CHECK-NEXT: %[[JOINED:.*]] = "llvm.mlir.constant"() <{"value" = 42 : i32}>
  // CHECK-NEXT: "func.return"(%[[JOINED]])

  "func.func"() <{function_type = (i1) -> i32, sym_name = "conflicting_join"}> ({
  ^entry(%cond : i1):
    %left = "arith.constant"() <{value = 1 : i32}> : () -> i32
    %right = "arith.constant"() <{value = 2 : i32}> : () -> i32
    %offset = "arith.constant"() <{value = 9 : i32}> : () -> i32
    "cf.cond_br"(%cond, %left, %offset, %right, %offset) [^join, ^join]
      <{operandSegmentSizes = array<i32: 1, 2, 2>}> : (i1, i32, i32, i32, i32) -> ()
  ^join(%value : i32, %offsetArg : i32):
    %result = "arith.addi"(%value, %offsetArg) : (i32, i32) -> i32
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @conflicting_join
  // CHECK: "cf.cond_br"
  // CHECK-NEXT: ^{{.*}}(%[[CONFLICT:[^ ]+]] : i32, %{{.*}}: i32):
  // CHECK-NEXT: %[[OFFSET:.*]] = "arith.constant"() <{"value" = 9 : i32}>
  // CHECK-NEXT: %[[CONFLICT_RESULT:.*]] = "arith.addi"(%[[CONFLICT]], %[[OFFSET]])
  // CHECK-NEXT: "func.return"(%[[CONFLICT_RESULT]])

  "func.func"() <{function_type = (i1, i32) -> i32, sym_name = "unknown_join"}> ({
  ^entry(%cond : i1, %unknown : i32):
    %known = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "cf.cond_br"(%cond, %known, %known, %unknown, %known) [^join, ^join]
      <{operandSegmentSizes = array<i32: 1, 2, 2>}> : (i1, i32, i32, i32, i32) -> ()
  ^join(%value : i32, %offset : i32):
    %result = "arith.addi"(%value, %offset) : (i32, i32) -> i32
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @unknown_join
  // CHECK: "cf.cond_br"
  // CHECK-NEXT: ^{{.*}}(%[[UNKNOWN:[^ ]+]] : i32, %{{.*}}: i32):
  // CHECK-NEXT: %[[KNOWN_OFFSET:.*]] = "arith.constant"() <{"value" = 7 : i32}>
  // CHECK-NEXT: %[[UNKNOWN_RESULT:.*]] = "arith.addi"(%[[UNKNOWN]], %[[KNOWN_OFFSET]])
  // CHECK-NEXT: "func.return"(%[[UNKNOWN_RESULT]])

  "func.func"() <{function_type = (i1) -> i32, sym_name = "constant_loop"}> ({
  ^entry(%cond : i1):
    %seven = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "cf.br"(%seven) [^loop] : (i32) -> ()
  ^loop(%value : i32):
    "cf.cond_br"(%cond, %value, %value) [^loop, ^exit]
      <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^exit(%result : i32):
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @constant_loop
  // CHECK: "cf.cond_br"
  // CHECK-NEXT: ^{{.*}}(%{{.*}}: i32):
  // CHECK-NEXT: %[[LOOP_RESULT:.*]] = "arith.constant"() <{"value" = 7 : i32}>
  // CHECK-NEXT: "func.return"(%[[LOOP_RESULT]])

  "func.func"() <{function_type = (i1) -> i32, sym_name = "varying_loop"}> ({
  ^entry(%cond : i1):
    %zero = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %one = "arith.constant"() <{value = 1 : i32}> : () -> i32
    "cf.br"(%zero, %one) [^loop] : (i32, i32) -> ()
  ^loop(%value : i32, %step : i32):
    %next = "arith.addi"(%value, %step) : (i32, i32) -> i32
    "cf.cond_br"(%cond, %next, %step, %value) [^loop, ^exit]
      <{operandSegmentSizes = array<i32: 1, 2, 1>}> : (i1, i32, i32, i32) -> ()
  ^exit(%result : i32):
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @varying_loop
  // CHECK: "cf.br"
  // CHECK-NEXT: ^{{.*}}(%[[LOOP_VALUE:[^ ]+]] : i32, %{{.*}}: i32):
  // CHECK-NEXT: %[[STEP:.*]] = "arith.constant"() <{"value" = 1 : i32}>
  // CHECK-NEXT: %[[NEXT:.*]] = "arith.addi"(%[[LOOP_VALUE]], %[[STEP]])
  // CHECK-NEXT: "cf.cond_br"(%{{.*}}, %[[NEXT]], %[[STEP]], %[[LOOP_VALUE]])
  // CHECK-NEXT: ^{{.*}}(%[[VARYING:[^ ]+]] : i32):
  // CHECK-NEXT: "func.return"(%[[VARYING]])

  "func.func"() <{function_type = () -> i32, sym_name = "late_predecessor"}> ({
  ^entry:
    "cf.br"() [^source] : () -> ()
  ^exit(%result : i32):
    "func.return"(%result) : (i32) -> ()
  ^source:
    %value = "arith.constant"() <{value = 19 : i32}> : () -> i32
    "cf.br"(%value) [^exit] : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @late_predecessor
  // CHECK: "cf.br"
  // CHECK-NEXT: ^{{.*}}(%{{.*}}: i32):
  // CHECK-NEXT: %[[LATE:.*]] = "arith.constant"() <{"value" = 19 : i32}>
  // CHECK-NEXT: "func.return"(%[[LATE]])

  "func.func"() <{function_type = (i8) -> (i8, i1), sym_name = "poison"}> ({
  ^entry(%unknown : i8):
    %poison = "llvm.mlir.poison"() : () -> i8
    "cf.br"(%poison) [^exit] : (i8) -> ()
  ^exit(%value : i8):
    %sum, %overflow = "arith.addui_extended"(%unknown, %value) : (i8, i8) -> (i8, i1)
    "test.test"(%sum) : (i8) -> ()
    "func.return"(%sum, %overflow) : (i8, i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @poison
  // CHECK: "cf.br"
  // CHECK-NEXT: ^{{.*}}(%{{.*}}: i8):
  // CHECK-NEXT: %[[POISON_SUM:.*]] = "llvm.mlir.poison"() : () -> i8
  // CHECK-NEXT: %[[POISON_FLAG:.*]] = "llvm.mlir.poison"() : () -> i1
  // CHECK-NEXT: "test.test"(%[[POISON_SUM]])
  // CHECK-NEXT: "func.return"(%[[POISON_SUM]], %[[POISON_FLAG]])

  "func.func"() <{function_type = () -> i32, sym_name = "llvm_result"}> ({
  ^entry:
    %value = "llvm.mlir.constant"() <{value = 41 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.br"(%value) [^exit] : (i32) -> ()
  ^exit(%input : i32):
    %result = "llvm.add"(%input, %one) : (i32, i32) -> i32
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @llvm_result
  // CHECK: "llvm.br"
  // CHECK-NEXT: ^{{.*}}(%{{.*}}: i32):
  // CHECK-NEXT: %[[LLVM_RESULT:.*]] = "llvm.mlir.constant"() <{"value" = 42 : i32}>
  // CHECK-NEXT: "func.return"(%[[LLVM_RESULT]])

  // The block argument keeps a surviving `llvm` user, so the materialized
  // constant must stay in the `llvm` dialect rather than reintroducing `arith`.
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "llvm_argument"}> ({
  ^entry(%ptr : !llvm.ptr):
    %value = "llvm.mlir.constant"() <{value = 41 : i32}> : () -> i32
    "llvm.br"(%value) [^exit] : (i32) -> ()
  ^exit(%input : i32):
    "llvm.store"(%input, %ptr) <{ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @llvm_argument
  // CHECK: "llvm.br"
  // CHECK-NEXT: ^{{.*}}(%{{.*}}: i32):
  // CHECK-NEXT: %[[LLVM_ARG:.*]] = "llvm.mlir.constant"() <{"value" = 41 : i32}>
  // CHECK-NEXT: "llvm.store"(%[[LLVM_ARG]]

  "func.func"() <{function_type = () -> !mod_arith.int<17 : i8>, sym_name = "modular_argument"}> ({
  ^entry:
    %value = "mod_arith.constant"() <{value = 3 : i8}> : () -> !mod_arith.int<17 : i8>
    "cf.br"(%value) [^exit] : (!mod_arith.int<17 : i8>) -> ()
  ^exit(%result : !mod_arith.int<17 : i8>):
    "func.return"(%result) : (!mod_arith.int<17 : i8>) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @modular_argument
  // CHECK: "cf.br"
  // CHECK-NEXT: ^{{.*}}(%{{.*}}: !mod_arith.int<17 : i8>):
  // CHECK-NEXT: %[[MOD_RESULT:.*]] = "mod_arith.constant"() <{"value" = 3 : i8}>
  // CHECK-NEXT: "func.return"(%[[MOD_RESULT]])

  "func.func"() <{function_type = (i32) -> (i1, i32), sym_name = "single_analysis"}> ({
  ^entry(%unknown : i32):
    %zero = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %offset = "arith.constant"() <{value = 9 : i32}> : () -> i32
    %sum, %carry = "arith.addui_extended"(%zero, %unknown) : (i32, i32) -> (i32, i1)
    "cf.br"(%carry, %offset) [^exit] : (i1, i32) -> ()
  ^exit(%value : i1, %offsetArg : i32):
    "func.return"(%value, %offsetArg) : (i1, i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @single_analysis
  // CHECK: "cf.br"
  // CHECK-NEXT: ^{{.*}}(%[[CARRY:[^ ]+]] : i1, %{{.*}}: i32):
  // CHECK-NEXT: %[[SNAPSHOT_OFFSET:.*]] = "arith.constant"() <{"value" = 9 : i32}>
  // CHECK-NEXT: "func.return"(%[[CARRY]], %[[SNAPSHOT_OFFSET]])
}) : () -> ()
