// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

"builtin.module"() ({

  // The commutative arith binops merge regardless of operand order;
  // `arith.subi` does not.
  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "binops"}> ({
  ^bb0(%a : i32, %b : i32):
    %add0 = "arith.addi"(%a, %b) : (i32, i32) -> i32
    %add1 = "arith.addi"(%b, %a) : (i32, i32) -> i32
    %mul0 = "arith.muli"(%a, %b) : (i32, i32) -> i32
    %mul1 = "arith.muli"(%b, %a) : (i32, i32) -> i32
    %and0 = "arith.andi"(%a, %b) : (i32, i32) -> i32
    %and1 = "arith.andi"(%b, %a) : (i32, i32) -> i32
    %or0 = "arith.ori"(%a, %b) : (i32, i32) -> i32
    %or1 = "arith.ori"(%b, %a) : (i32, i32) -> i32
    %xor0 = "arith.xori"(%a, %b) : (i32, i32) -> i32
    %xor1 = "arith.xori"(%b, %a) : (i32, i32) -> i32
    %max0 = "arith.maxsi"(%a, %b) : (i32, i32) -> i32
    %max1 = "arith.maxsi"(%b, %a) : (i32, i32) -> i32
    %min0 = "arith.minui"(%a, %b) : (i32, i32) -> i32
    %min1 = "arith.minui"(%b, %a) : (i32, i32) -> i32
    %sub0 = "arith.subi"(%a, %b) : (i32, i32) -> i32
    %sub1 = "arith.subi"(%a, %b) : (i32, i32) -> i32
    %sub2 = "arith.subi"(%b, %a) : (i32, i32) -> i32
    "test.test"(%add0, %add1, %mul0, %mul1, %and0, %and1, %or0, %or1, %xor0, %xor1, %max0, %max1, %min0, %min1, %sub0, %sub1, %sub2) : (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @binops(
    // CHECK:      %[[ADD:.*]] = "arith.addi"(%[[A:[^ ]*]], %[[B:[^ ]*]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[MUL:.*]] = "arith.muli"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[AND:.*]] = "arith.andi"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[OR:.*]] = "arith.ori"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[XOR:.*]] = "arith.xori"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[MAX:.*]] = "arith.maxsi"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[MIN:.*]] = "arith.minui"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[SUB:.*]] = "arith.subi"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[SUBR:.*]] = "arith.subi"(%[[B]], %[[A]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD]], %[[ADD]], %[[MUL]], %[[MUL]], %[[AND]], %[[AND]], %[[OR]], %[[OR]], %[[XOR]], %[[XOR]], %[[MAX]], %[[MAX]], %[[MIN]], %[[MIN]], %[[SUB]], %[[SUB]], %[[SUBR]])
  }) : () -> ()

  // UB flags partition identity: differently-flagged ops never merge, but
  // commutativity still applies between ops carrying matching flags.
  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "flags"}> ({
  ^bb0(%a : i32, %b : i32):
    %add_plain = "arith.addi"(%a, %b) : (i32, i32) -> i32
    %add_nsw = "arith.addi"(%a, %b) <{"overflowFlags" = #arith.overflow<nsw>}> : (i32, i32) -> i32
    %add_nsw_comm = "arith.addi"(%b, %a) <{"overflowFlags" = #arith.overflow<nsw>}> : (i32, i32) -> i32
    %add_nuw = "arith.addi"(%a, %b) <{"overflowFlags" = #arith.overflow<nuw>}> : (i32, i32) -> i32
    %add_both = "arith.addi"(%a, %b) <{"overflowFlags" = #arith.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %or_plain = "arith.ori"(%a, %b) : (i32, i32) -> i32
    %or_disjoint = "arith.ori"(%a, %b) <{disjoint}> : (i32, i32) -> i32
    %or_disjoint_comm = "arith.ori"(%b, %a) <{disjoint}> : (i32, i32) -> i32
    %div_plain = "arith.divsi"(%a, %b) : (i32, i32) -> i32
    %div_exact_1 = "arith.divsi"(%a, %b) <{exact}> : (i32, i32) -> i32
    %div_exact_2 = "arith.divsi"(%a, %b) <{exact}> : (i32, i32) -> i32
    "test.test"(%add_plain, %add_nsw, %add_nsw_comm, %add_nuw, %add_both, %or_plain, %or_disjoint, %or_disjoint_comm, %div_plain, %div_exact_1, %div_exact_2) : (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @flags(
    // CHECK:      %[[ADD_PLAIN:.*]] = "arith.addi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[ADD_NSW:.*]] = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nsw>}>
    // CHECK-NEXT: %[[ADD_NUW:.*]] = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nuw>}>
    // CHECK-NEXT: %[[ADD_BOTH:.*]] = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nsw, nuw>}>
    // CHECK-NEXT: %[[OR_PLAIN:.*]] = "arith.ori"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[OR_DISJOINT:.*]] = "arith.ori"(%{{.*}}, %{{.*}}) <{disjoint}>
    // CHECK-NEXT: %[[DIV_PLAIN:.*]] = "arith.divsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[DIV_EXACT:.*]] = "arith.divsi"(%{{.*}}, %{{.*}}) <{exact}>
    // CHECK-NEXT: "test.test"(%[[ADD_PLAIN]], %[[ADD_NSW]], %[[ADD_NSW]], %[[ADD_NUW]], %[[ADD_BOTH]], %[[OR_PLAIN]], %[[OR_DISJOINT]], %[[OR_DISJOINT]], %[[DIV_PLAIN]], %[[DIV_EXACT]], %[[DIV_EXACT]])
  }) : () -> ()

  // `arith.cmpi` predicates are canonicalized the same way `llvm.icmp`'s are:
  // a "greater" comparison is the swapped-operand "less" comparison, and
  // eq/ne are commutative. A same-predicate comparison with swapped operands
  // stays distinct.
  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "cmpi"}> ({
  ^bb0(%a : i32, %b : i32):
    %sgt = "arith.cmpi"(%a, %b) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
    %slt_swapped = "arith.cmpi"(%b, %a) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    %sge = "arith.cmpi"(%a, %b) <{"predicate" = 5 : i64}> : (i32, i32) -> i1
    %sle_swapped = "arith.cmpi"(%b, %a) <{"predicate" = 3 : i64}> : (i32, i32) -> i1
    %ugt = "arith.cmpi"(%a, %b) <{"predicate" = 8 : i64}> : (i32, i32) -> i1
    %ult_swapped = "arith.cmpi"(%b, %a) <{"predicate" = 6 : i64}> : (i32, i32) -> i1
    %uge = "arith.cmpi"(%a, %b) <{"predicate" = 9 : i64}> : (i32, i32) -> i1
    %ule_swapped = "arith.cmpi"(%b, %a) <{"predicate" = 7 : i64}> : (i32, i32) -> i1
    %eq = "arith.cmpi"(%a, %b) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
    %eq_comm = "arith.cmpi"(%b, %a) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
    %ne = "arith.cmpi"(%a, %b) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
    %ne_comm = "arith.cmpi"(%b, %a) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
    %slt = "arith.cmpi"(%a, %b) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    "test.test"(%sgt, %slt_swapped, %sge, %sle_swapped, %ugt, %ult_swapped, %uge, %ule_swapped, %eq, %eq_comm, %ne, %ne_comm, %slt) : (i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @cmpi(
    // CHECK:      %[[SGT:.*]] = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 4 : i64}>
    // CHECK-NEXT: %[[SGE:.*]] = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 5 : i64}>
    // CHECK-NEXT: %[[UGT:.*]] = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 8 : i64}>
    // CHECK-NEXT: %[[UGE:.*]] = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 9 : i64}>
    // CHECK-NEXT: %[[EQ:.*]] = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}>
    // CHECK-NEXT: %[[NE:.*]] = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 1 : i64}>
    // CHECK-NEXT: %[[SLT:.*]] = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}>
    // CHECK-NEXT: "test.test"(%[[SGT]], %[[SGT]], %[[SGE]], %[[SGE]], %[[UGT]], %[[UGT]], %[[UGE]], %[[UGE]], %[[EQ]], %[[EQ]], %[[NE]], %[[NE]], %[[SLT]])
  }) : () -> ()

  // Constants merge only when both value and type agree; the casts key on
  // their result type, so widening to different types stays distinct.
  "func.func"() <{function_type = (i32) -> (), sym_name = "constants_and_casts"}> ({
  ^bb0(%a : i32):
    %c7_a = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
    %c7_b = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
    %c8 = "arith.constant"() <{"value" = 8 : i32}> : () -> i32
    %c7_i8 = "arith.constant"() <{"value" = 7 : i8}> : () -> i8
    %zext_1 = "arith.extui"(%c7_i8) : (i8) -> i32
    %zext_2 = "arith.extui"(%c7_i8) : (i8) -> i32
    %zext_nneg = "arith.extui"(%c7_i8) <{nneg}> : (i8) -> i32
    %sext = "arith.extsi"(%c7_i8) : (i8) -> i32
    %zext_i16 = "arith.extui"(%c7_i8) : (i8) -> i16
    %trunc_1 = "arith.trunci"(%a) : (i32) -> i8
    %trunc_2 = "arith.trunci"(%a) : (i32) -> i8
    %trunc_nsw = "arith.trunci"(%a) <{"overflowFlags" = #arith.overflow<nsw>}> : (i32) -> i8
    "test.test"(%c7_a, %c7_b, %c8, %c7_i8, %zext_1, %zext_2, %zext_nneg, %sext, %zext_i16, %trunc_1, %trunc_2, %trunc_nsw) : (i32, i32, i32, i8, i32, i32, i32, i32, i16, i8, i8, i8) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @constants_and_casts(
    // CHECK:      %[[C7:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
    // CHECK-NEXT: %[[C8:.*]] = "arith.constant"() <{"value" = 8 : i32}> : () -> i32
    // CHECK-NEXT: %[[C7_I8:.*]] = "arith.constant"() <{"value" = 7 : i8}> : () -> i8
    // CHECK-NEXT: %[[ZEXT:.*]] = "arith.extui"(%[[C7_I8]]) : (i8) -> i32
    // CHECK-NEXT: %[[ZEXT_NNEG:.*]] = "arith.extui"(%[[C7_I8]]) <{nneg}> : (i8) -> i32
    // CHECK-NEXT: %[[SEXT:.*]] = "arith.extsi"(%[[C7_I8]]) : (i8) -> i32
    // CHECK-NEXT: %[[ZEXT_I16:.*]] = "arith.extui"(%[[C7_I8]]) : (i8) -> i16
    // CHECK-NEXT: %[[TRUNC:.*]] = "arith.trunci"(%{{.*}}) : (i32) -> i8
    // CHECK-NEXT: %[[TRUNC_NSW:.*]] = "arith.trunci"(%{{.*}}) <{"overflowFlags" = #arith.overflow<nsw>}>
    // CHECK-NEXT: "test.test"(%[[C7]], %[[C7]], %[[C8]], %[[C7_I8]], %[[ZEXT]], %[[ZEXT]], %[[ZEXT_NNEG]], %[[SEXT]], %[[ZEXT_I16]], %[[TRUNC]], %[[TRUNC]], %[[TRUNC_NSW]])
  }) : () -> ()

  // `arith.select` is not commutative in its value operands.
  "func.func"() <{function_type = (i1, i32, i32) -> (), sym_name = "select"}> ({
  ^bb0(%c : i1, %a : i32, %b : i32):
    %sel0 = "arith.select"(%c, %a, %b) : (i1, i32, i32) -> i32
    %sel1 = "arith.select"(%c, %a, %b) : (i1, i32, i32) -> i32
    %sel_swapped = "arith.select"(%c, %b, %a) : (i1, i32, i32) -> i32
    "test.test"(%sel0, %sel1, %sel_swapped) : (i32, i32, i32) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @select(
    // CHECK:      %[[SEL:.*]] = "arith.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[SEL_SWAPPED:.*]] = "arith.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SEL]], %[[SEL]], %[[SEL_SWAPPED]])
  }) : () -> ()

  // The opcode is part of the Key, so an arith op never merges with the
  // corresponding LLVM op even though they compute the same thing.
  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "cross_dialect"}> ({
  ^bb0(%a : i32, %b : i32):
    %arith_add = "arith.addi"(%a, %b) : (i32, i32) -> i32
    %llvm_add = "llvm.add"(%a, %b) : (i32, i32) -> i32
    %arith_eq = "arith.cmpi"(%a, %b) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
    %llvm_eq = "llvm.icmp"(%a, %b) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
    "test.test"(%arith_add, %llvm_add, %arith_eq, %llvm_eq) : (i32, i32, i1, i1) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @cross_dialect(
    // CHECK:      %[[ARITH_ADD:.*]] = "arith.addi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[LLVM_ADD:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[ARITH_EQ:.*]] = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}>
    // CHECK-NEXT: %[[LLVM_EQ:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}>
    // CHECK-NEXT: "test.test"(%[[ARITH_ADD]], %[[LLVM_ADD]], %[[ARITH_EQ]], %[[LLVM_EQ]])
  }) : () -> ()

}) : () -> ()
