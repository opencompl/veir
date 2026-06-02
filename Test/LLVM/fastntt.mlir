// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// This test results from the lowering of a C implementation of the FastNTT algorithm, based on the Heir 
// pseudocode: https://github.com/google/heir/blob/1210ad37dc9531d6e60d8ddbce81dbd79f7626a6/lib/Dialect/Polynomial/Conversions/PolynomialToModArith/PolynomialToModArith.cpp#L1060. 
// We detail the flags and specifics of the lowering from C to LLVM IR in https://github.com/opencompl/veir/pull/458

"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (ptr, i64, i64, ptr, i64, i64)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "fastNTT", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: i64, %arg2: i64, %arg3: !llvm.ptr, %arg4: i64, %arg5: i64):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %3 = "llvm.icmp"(%arg4, %0) <{predicate = 1 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%3)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    "llvm.br"(%arg1)[^bb3] : (i64) -> ()
  ^bb2:  // pred: ^bb0
    "llvm.br"(%1)[^bb3] : (i64) -> ()
  ^bb3(%4: i64):  // 2 preds: ^bb1, ^bb2
    %5 = "llvm.icmp"(%arg4, %0) <{predicate = 1 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%5)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    "llvm.br"(%2)[^bb6] : (i64) -> ()
  ^bb5:  // pred: ^bb3
    %6 = "llvm.sdiv"(%arg5, %1) : (i64, i64) -> i64
    "llvm.br"(%6)[^bb6] : (i64) -> ()
  ^bb6(%7: i64):  // 2 preds: ^bb4, ^bb5
    %8 = "llvm.sdiv"(%arg1, %1) : (i64, i64) -> i64
    "llvm.br"(%4, %7, %8, %0)[^bb7] : (i64, i64, i64, i64) -> ()
  ^bb7(%9: i64, %10: i64, %11: i64, %12: i64):  // 2 preds: ^bb6, ^bb26
    "llvm.br"(%0, %arg1)[^bb8] : (i64, i64) -> ()
  ^bb8(%13: i64, %14: i64):  // 2 preds: ^bb7, ^bb9
    %15 = "llvm.icmp"(%14, %2) <{predicate = 4 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%15)[^bb9, ^bb10] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb9:  // pred: ^bb8
    %16 = "llvm.ashr"(%14, %2) : (i64, i64) -> i64
    %17 = "llvm.add"(%13, %2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.br"(%17, %16)[^bb8] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i64, i64) -> ()
  ^bb10:  // pred: ^bb8
    %18 = "llvm.icmp"(%12, %13) <{predicate = 2 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%18)[^bb11, ^bb27] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb11:  // pred: ^bb10
    "llvm.br"(%0)[^bb12] : (i64) -> ()
  ^bb12(%19: i64):  // 2 preds: ^bb11, ^bb18
    %20 = "llvm.sdiv"(%arg1, %9) : (i64, i64) -> i64
    %21 = "llvm.icmp"(%19, %20) <{predicate = 2 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%21)[^bb13, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb13:  // pred: ^bb12
    "llvm.br"(%0)[^bb14] : (i64) -> ()
  ^bb14(%22: i64):  // 2 preds: ^bb13, ^bb16
    %23 = "llvm.sdiv"(%9, %1) : (i64, i64) -> i64
    %24 = "llvm.icmp"(%22, %23) <{predicate = 2 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%24)[^bb15, ^bb17] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb15:  // pred: ^bb14
    %25 = "llvm.mul"(%19, %9) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %26 = "llvm.add"(%25, %22) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %27 = "llvm.getelementptr"(%arg0, %26) <{elem_type = i64, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %28 = "llvm.load"(%27) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %29 = "llvm.mul"(%19, %9) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %30 = "llvm.add"(%29, %22) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %31 = "llvm.sdiv"(%9, %1) : (i64, i64) -> i64
    %32 = "llvm.add"(%30, %31) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %33 = "llvm.getelementptr"(%arg0, %32) <{elem_type = i64, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %34 = "llvm.load"(%33) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %35 = "llvm.mul"(%1, %22) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %36 = "llvm.add"(%35, %2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %37 = "llvm.mul"(%36, %11) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %38 = "llvm.getelementptr"(%arg3, %37) <{elem_type = i64, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %39 = "llvm.load"(%38) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %40 = "llvm.mul"(%39, %34) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %41 = "llvm.srem"(%40, %arg2) : (i64, i64) -> i64
    %42 = "llvm.add"(%28, %41) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %43 = "llvm.srem"(%42, %arg2) : (i64, i64) -> i64
    %44 = "llvm.mul"(%39, %34) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %45 = "llvm.srem"(%44, %arg2) : (i64, i64) -> i64
    %46 = "llvm.sub"(%28, %45) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %47 = "llvm.add"(%46, %arg2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %48 = "llvm.srem"(%47, %arg2) : (i64, i64) -> i64
    %49 = "llvm.mul"(%19, %9) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %50 = "llvm.add"(%49, %22) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %51 = "llvm.getelementptr"(%arg0, %50) <{elem_type = i64, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%43, %51) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %52 = "llvm.mul"(%19, %9) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %53 = "llvm.add"(%52, %22) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %54 = "llvm.sdiv"(%9, %1) : (i64, i64) -> i64
    %55 = "llvm.add"(%53, %54) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %56 = "llvm.getelementptr"(%arg0, %55) <{elem_type = i64, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%48, %56) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.br"()[^bb16] : () -> ()
  ^bb16:  // pred: ^bb15
    %57 = "llvm.add"(%22, %2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.br"(%57)[^bb14] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i64) -> ()
  ^bb17:  // pred: ^bb14
    "llvm.br"()[^bb18] : () -> ()
  ^bb18:  // pred: ^bb17
    %58 = "llvm.add"(%19, %2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.br"(%58)[^bb12] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i64) -> ()
  ^bb19:  // pred: ^bb12
    %59 = "llvm.sdiv"(%11, %1) : (i64, i64) -> i64
    %60 = "llvm.icmp"(%arg4, %0) <{predicate = 1 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%60)[^bb20, ^bb21] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb20:  // pred: ^bb19
    %61 = "llvm.sdiv"(%9, %1) : (i64, i64) -> i64
    "llvm.br"(%61)[^bb22] : (i64) -> ()
  ^bb21:  // pred: ^bb19
    %62 = "llvm.mul"(%9, %1) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.br"(%62)[^bb22] : (i64) -> ()
  ^bb22(%63: i64):  // 2 preds: ^bb20, ^bb21
    %64 = "llvm.icmp"(%arg4, %0) <{predicate = 1 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%64)[^bb23, ^bb24] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb23:  // pred: ^bb22
    %65 = "llvm.mul"(%10, %1) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.br"(%65)[^bb25] : (i64) -> ()
  ^bb24:  // pred: ^bb22
    %66 = "llvm.sdiv"(%10, %1) : (i64, i64) -> i64
    "llvm.br"(%66)[^bb25] : (i64) -> ()
  ^bb25(%67: i64):  // 2 preds: ^bb23, ^bb24
    "llvm.br"()[^bb26] : () -> ()
  ^bb26:  // pred: ^bb25
    %68 = "llvm.add"(%12, %2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.br"(%63, %67, %59, %68)[^bb7] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i64, i64, i64, i64) -> ()
  ^bb27:  // pred: ^bb10
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "Ubuntu clang version 18.1.3 (1ubuntu1)", llvm.module_asm = [], llvm.target_triple = "x86_64-pc-linux-gnu"} : () -> ()

// CHECK: "llvm.func"() <{{{.*}}"function_type" = !llvm.func<void (!llvm.ptr, i64, i64, !llvm.ptr, i64, i64)>,{{.*}}"sym_name" = "fastNTT"{{.*}}}> ({
// CHECK-NEXT: ^{{.*}}(%[[COEFFS:.*]] : !llvm.ptr, %[[N:.*]] : i64, %[[CMOD:.*]] : i64, %[[ROOTS:.*]] : !llvm.ptr, %[[INVERSE:.*]] : i64, %[[DEGREE:.*]] : i64):
// CHECK-NEXT: %[[C0:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT: %[[C2:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT: %[[C1:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: %[[COND0:.*]] = "llvm.icmp"(%[[INVERSE]], %[[C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT: "llvm.cond_br"(%[[COND0]]) [^[[BB12:.*]], ^[[BB13:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT: ^[[BB12]]():
// CHECK-NEXT: "llvm.br"(%[[N]]) [^[[BB15:.*]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB13]]():
// CHECK-NEXT: "llvm.br"(%[[C2]]) [^[[BB15]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB15]](%[[M_VAL:.*]] : i64):
// CHECK-NEXT: %[[COND1:.*]] = "llvm.icmp"(%[[INVERSE]], %[[C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT: "llvm.cond_br"(%[[COND1]]) [^[[BB19:.*]], ^[[BB20:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT: ^[[BB19]]():
// CHECK-NEXT: "llvm.br"(%[[C1]]) [^[[BB22:.*]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB20]]():
// CHECK-NEXT: %[[DEG_DIV2:.*]] = "llvm.sdiv"(%[[DEGREE]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[DEG_DIV2]]) [^[[BB22]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB22]](%[[R_VAL:.*]] : i64):
// CHECK-NEXT: %[[N_DIV2:.*]] = "llvm.sdiv"(%[[N]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[M_VAL]], %[[R_VAL]], %[[N_DIV2]], %[[C0]]) [^[[BB27:.*]]] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT: ^[[BB27]](%[[ARG_M:.*]] : i64, %[[ARG_R:.*]] : i64, %[[ARG_EXP:.*]] : i64, %[[ARG_S:.*]] : i64):
// CHECK-NEXT: "llvm.br"(%[[C0]], %[[N]]) [^[[BB29:.*]]] : (i64, i64) -> ()
// CHECK-NEXT: ^[[BB29]](%[[LOG_RES:.*]] : i64, %[[LOG_N:.*]] : i64):
// CHECK-NEXT: %[[LOG_COND:.*]] = "llvm.icmp"(%[[LOG_N]], %[[C1]]) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
// CHECK-NEXT: "llvm.cond_br"(%[[LOG_COND]]) [^[[BB32:.*]], ^[[BB33:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT: ^[[BB32]]():
// CHECK-NEXT: %[[LOG_SHR:.*]] = "llvm.ashr"(%[[LOG_N]], %[[C1]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[LOG_ADD:.*]] = "llvm.add"(%[[LOG_RES]], %[[C1]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[LOG_ADD]], %[[LOG_SHR]]) [^[[BB29]]] : (i64, i64) -> ()
// CHECK-NEXT: ^[[BB33]]():
// CHECK-NEXT: %[[LOOP_S_COND:.*]] = "llvm.icmp"(%[[ARG_S]], %[[LOG_RES]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT: "llvm.cond_br"(%[[LOOP_S_COND]]) [^[[BB39:.*]], ^[[BB40:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT: ^[[BB39]]():
// CHECK-NEXT: "llvm.br"(%[[C0]]) [^[[BB42:.*]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB42]](%[[LOOP_K:.*]] : i64):
// CHECK-NEXT: %[[N_DIV_M:.*]] = "llvm.sdiv"(%[[N]], %[[ARG_M]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[LOOP_K_COND:.*]] = "llvm.icmp"(%[[LOOP_K]], %[[N_DIV_M]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT: "llvm.cond_br"(%[[LOOP_K_COND]]) [^[[BB46:.*]], ^[[BB47:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT: ^[[BB46]]():
// CHECK-NEXT: "llvm.br"(%[[C0]]) [^[[BB49:.*]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB49]](%[[LOOP_J:.*]] : i64):
// CHECK-NEXT: %[[M_DIV2:.*]] = "llvm.sdiv"(%[[ARG_M]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[LOOP_J_COND:.*]] = "llvm.icmp"(%[[LOOP_J]], %[[M_DIV2]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT: "llvm.cond_br"(%[[LOOP_J_COND]]) [^[[BB53:.*]], ^[[BB54:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT: ^[[BB53]]():
// CHECK-NEXT: %[[T56:.*]] = "llvm.mul"(%[[LOOP_K]], %[[ARG_M]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T57:.*]] = "llvm.add"(%[[T56]], %[[LOOP_J]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[GEP_A:.*]] = "llvm.getelementptr"(%[[COEFFS]], %[[T57]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT: %[[VAL_A:.*]] = "llvm.load"(%[[GEP_A]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT: %[[T60:.*]] = "llvm.mul"(%[[LOOP_K]], %[[ARG_M]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T61:.*]] = "llvm.add"(%[[T60]], %[[LOOP_J]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T62:.*]] = "llvm.sdiv"(%[[ARG_M]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[T63:.*]] = "llvm.add"(%[[T61]], %[[T62]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[GEP_B:.*]] = "llvm.getelementptr"(%[[COEFFS]], %[[T63]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT: %[[VAL_B:.*]] = "llvm.load"(%[[GEP_B]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT: %[[T66:.*]] = "llvm.mul"(%[[C2]], %[[LOOP_J]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T67:.*]] = "llvm.add"(%[[T66]], %[[C1]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T68:.*]] = "llvm.mul"(%[[T67]], %[[ARG_EXP]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[GEP_ROOT:.*]] = "llvm.getelementptr"(%[[ROOTS]], %[[T68]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT: %[[VAL_ROOT:.*]] = "llvm.load"(%[[GEP_ROOT]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT: %[[T71:.*]] = "llvm.mul"(%[[VAL_ROOT]], %[[VAL_B]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T72:.*]] = "llvm.srem"(%[[T71]], %[[CMOD]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[T73:.*]] = "llvm.add"(%[[VAL_A]], %[[T72]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[OUT_A:.*]] = "llvm.srem"(%[[T73]], %[[CMOD]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[T75:.*]] = "llvm.mul"(%[[VAL_ROOT]], %[[VAL_B]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T76:.*]] = "llvm.srem"(%[[T75]], %[[CMOD]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[T77:.*]] = "llvm.sub"(%[[VAL_A]], %[[T76]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T78:.*]] = "llvm.add"(%[[T77]], %[[CMOD]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[OUT_B:.*]] = "llvm.srem"(%[[T78]], %[[CMOD]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[T80:.*]] = "llvm.mul"(%[[LOOP_K]], %[[ARG_M]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T81:.*]] = "llvm.add"(%[[T80]], %[[LOOP_J]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[GEP_STORE_A:.*]] = "llvm.getelementptr"(%[[COEFFS]], %[[T81]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT: "llvm.store"(%[[OUT_A]], %[[GEP_STORE_A]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT: %[[T84:.*]] = "llvm.mul"(%[[LOOP_K]], %[[ARG_M]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T85:.*]] = "llvm.add"(%[[T84]], %[[LOOP_J]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[T86:.*]] = "llvm.sdiv"(%[[ARG_M]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[T87:.*]] = "llvm.add"(%[[T85]], %[[T86]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: %[[GEP_STORE_B:.*]] = "llvm.getelementptr"(%[[COEFFS]], %[[T87]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT: "llvm.store"(%[[OUT_B]], %[[GEP_STORE_B]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT: "llvm.br"() [^[[BB90:.*]]] : () -> ()
// CHECK-NEXT: ^[[BB90]]():
// CHECK-NEXT: %[[NEXT_J:.*]] = "llvm.add"(%[[LOOP_J]], %[[C1]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[NEXT_J]]) [^[[BB49]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB54]]():
// CHECK-NEXT: "llvm.br"() [^[[BB94:.*]]] : () -> ()
// CHECK-NEXT: ^[[BB94]]():
// CHECK-NEXT: %[[NEXT_K:.*]] = "llvm.add"(%[[LOOP_K]], %[[C1]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[NEXT_K]]) [^[[BB42]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB47]]():
// CHECK-NEXT: %[[NEXT_EXP:.*]] = "llvm.sdiv"(%[[ARG_EXP]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[INV_COND:.*]] = "llvm.icmp"(%[[INVERSE]], %[[C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT: "llvm.cond_br"(%[[INV_COND]]) [^[[BB100:.*]], ^[[BB101:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT: ^[[BB100]]():
// CHECK-NEXT: %[[M_DIV2_NEXT:.*]] = "llvm.sdiv"(%[[ARG_M]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[M_DIV2_NEXT]]) [^[[BB104:.*]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB101]]():
// CHECK-NEXT: %[[M_MUL2_NEXT:.*]] = "llvm.mul"(%[[ARG_M]], %[[C2]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[M_MUL2_NEXT]]) [^[[BB104]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB104]](%[[NEXT_M:.*]] : i64):
// CHECK-NEXT: %[[INV_COND2:.*]] = "llvm.icmp"(%[[INVERSE]], %[[C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT: "llvm.cond_br"(%[[INV_COND2]]) [^[[BB109:.*]], ^[[BB110:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT: ^[[BB109]]():
// CHECK-NEXT: %[[R_MUL2_NEXT:.*]] = "llvm.mul"(%[[ARG_R]], %[[C2]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[R_MUL2_NEXT]]) [^[[BB113:.*]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB110]]():
// CHECK-NEXT: %[[R_DIV2_NEXT:.*]] = "llvm.sdiv"(%[[ARG_R]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[R_DIV2_NEXT]]) [^[[BB113]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB113]](%[[NEXT_R:.*]] : i64):
// CHECK-NEXT: "llvm.br"() [^[[BB117:.*]]] : () -> ()
// CHECK-NEXT: ^[[BB117]]():
// CHECK-NEXT: %[[NEXT_S:.*]] = "llvm.add"(%[[ARG_S]], %[[C1]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT: "llvm.br"(%[[NEXT_M]], %[[NEXT_R]], %[[NEXT_EXP]], %[[NEXT_S]]) [^[[BB27]]] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT: ^[[BB40]]():
// CHECK-NEXT: "llvm.return"() : () -> ()