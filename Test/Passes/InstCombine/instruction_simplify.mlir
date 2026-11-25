// RUN: veir-opt %s --print-op-generic -p='apply-patterns{and_two_same_masks_drop_one xor_pair_common_operand_cancel select_eq_const_identity select_true_false select_sgt_nsw_add_const_to_smax_nsw_add}' | filecheck %s

"builtin.module"() ({
  // Distinct constant operations with equal bits satisfy a repeated constant
  // capture. Both the inner and outer commutative nodes are reversed.
  "func.func"() <{sym_name = "equal_masks", function_type = (i8, i8) -> i8}> ({
  ^bb0(%x: i8, %y: i8):
    %c1 = "llvm.mlir.constant"() <{value = 15 : i8}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 15 : i8}> : () -> i8
    %a = "llvm.and"(%c1, %x) : (i8, i8) -> i8
    %b = "llvm.and"(%c2, %y) : (i8, i8) -> i8
    %r = "llvm.and"(%b, %a) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "equal_masks"
  // CHECK: "llvm.and"
  // CHECK: "llvm.and"
  // CHECK-NOT: "llvm.and"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "different_masks", function_type = (i8, i8) -> i8}> ({
  ^bb0(%x: i8, %y: i8):
    %c1 = "llvm.mlir.constant"() <{value = 15 : i8}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %a = "llvm.and"(%x, %c1) : (i8, i8) -> i8
    %b = "llvm.and"(%y, %c2) : (i8, i8) -> i8
    %r = "llvm.and"(%a, %b) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "different_masks"
  // CHECK: "llvm.and"
  // CHECK: "llvm.and"
  // CHECK: "llvm.and"
  // CHECK: "func.return"

  // Requiring one use counts operand occurrences, not distinct users.
  "func.func"() <{sym_name = "two_uses_one_user", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = 15 : i8}> : () -> i8
    %a = "llvm.and"(%x, %c) : (i8, i8) -> i8
    %r = "llvm.and"(%a, %a) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "two_uses_one_user"
  // CHECK: %[[A:[0-9]+]] = "llvm.and"
  // CHECK: "llvm.and"(%[[A]], %[[A]])

  // Ordinary repeated captures still require SSA identity.
  "func.func"() <{sym_name = "xor_same_value", function_type = (i8, i8, i8) -> i8}> ({
  ^bb0(%a: i8, %b: i8, %c: i8):
    %l = "llvm.xor"(%c, %a) : (i8, i8) -> i8
    %r = "llvm.xor"(%b, %c) : (i8, i8) -> i8
    %v = "llvm.xor"(%r, %l) : (i8, i8) -> i8
    "func.return"(%v) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "xor_same_value"
  // CHECK: "llvm.xor"
  // CHECK-NOT: "llvm.xor"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "xor_distinct_values", function_type = (i8, i8, i8, i8) -> i8}> ({
  ^bb0(%a: i8, %b: i8, %c: i8, %d: i8):
    %l = "llvm.xor"(%a, %c) : (i8, i8) -> i8
    %r = "llvm.xor"(%b, %d) : (i8, i8) -> i8
    %v = "llvm.xor"(%l, %r) : (i8, i8) -> i8
    "func.return"(%v) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "xor_distinct_values"
  // CHECK: "llvm.xor"
  // CHECK: "llvm.xor"
  // CHECK: "llvm.xor"

  "func.func"() <{sym_name = "constant_bits", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %c1 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %c2 = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i8
    %eq = "llvm.icmp"(%c1, %x) <{predicate = 0 : i64}> : (i8, i8) -> i1
    %r = "llvm.select"(%eq, %c2, %x) : (i1, i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "constant_bits"
  // CHECK-NOT: "llvm.
  // CHECK: "func.return"(%arg{{[0-9]+}}_0)

  // Returning the condition is legal only when the selected type is i1.
  "func.func"() <{sym_name = "wide_boolean_select", function_type = (i1) -> i8}> ({
  ^bb0(%c: i1):
    %one = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %zero = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %r = "llvm.select"(%c, %one, %zero) : (i1, i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "wide_boolean_select"
  // CHECK: "llvm.select"

  "func.func"() <{sym_name = "clamp_nsw", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %bound = "llvm.mlir.constant"() <{value = 10 : i8}> : () -> i8
    %addend = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %endpoint = "llvm.mlir.constant"() <{value = 13 : i8}> : () -> i8
    %c = "llvm.icmp"(%x, %bound) <{predicate = 4 : i64}> : (i8, i8) -> i1
    %a = "llvm.add"(%addend, %x) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %r = "llvm.select"(%c, %a, %endpoint) : (i1, i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "clamp_nsw"
  // CHECK-NOT: "llvm.icmp"
  // CHECK: "llvm.intr.smax"
  // CHECK: "llvm.add"{{.*}}"overflowFlags" = 1 : i32
  // CHECK-NOT: "llvm.select"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "overflowing_endpoint", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %bound = "llvm.mlir.constant"() <{value = 127 : i8}> : () -> i8
    %addend = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %endpoint = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %c = "llvm.icmp"(%x, %bound) <{predicate = 4 : i64}> : (i8, i8) -> i1
    %a = "llvm.add"(%x, %addend) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %r = "llvm.select"(%c, %a, %endpoint) : (i1, i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "overflowing_endpoint"
  // CHECK: "llvm.icmp"
  // CHECK: "llvm.add"
  // CHECK: "llvm.select"
}) : () -> ()
