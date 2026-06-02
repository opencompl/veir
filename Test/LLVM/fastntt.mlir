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

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^[[BB_MOD:.*]]():
// CHECK-NEXT:     "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}}> ({
// CHECK-NEXT:       ^[[BB_L2FA_ENTRY:.*]]([[L2FA_ARG:%.*]] : i32):
// CHECK-NEXT:         [[L2FA_C0:%.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         [[L2FA_C1:%.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         "llvm.br"([[L2FA_C0]], [[L2FA_ARG]]) [^[[BB_L2FA_COND:.*]]] : (i32, i32) -> ()
// CHECK-NEXT:       ^[[BB_L2FA_COND]]([[L2FA_V0:%.*]] : i32, [[L2FA_V1:%.*]] : i32):
// CHECK-NEXT:         [[L2FA_CMP:%.*]] = "llvm.icmp"([[L2FA_V1]], [[L2FA_C1]]) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"([[L2FA_CMP]]) [^[[BB_L2FA_BODY:.*]], ^[[BB_L2FA_EXIT:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[BB_L2FA_BODY]]():
// CHECK-NEXT:         [[L2FA_SHR:%.*]] = "llvm.ashr"([[L2FA_V1]], [[L2FA_C1]]) : (i32, i32) -> i32
// CHECK-NEXT:         [[L2FA_ADD:%.*]] = "llvm.add"([[L2FA_V0]], [[L2FA_C1]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"([[L2FA_ADD]], [[L2FA_SHR]]) [^[[BB_L2FA_COND]]] : (i32, i32) -> ()
// CHECK-NEXT:       ^[[BB_L2FA_EXIT]]():
// CHECK-NEXT:         "llvm.return"([[L2FA_V0]]) : (i32) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}}> ({
// CHECK-NEXT:       ^[[BB_L2F_ENTRY:.*]]([[L2F_ARG:%.*]] : i32):
// CHECK-NEXT:         [[L2F_C0:%.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         [[L2F_C1:%.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         "llvm.br"([[L2F_C0]], [[L2F_ARG]]) [^[[BB_L2F_COND:.*]]] : (i32, i32) -> ()
// CHECK-NEXT:       ^[[BB_L2F_COND]]([[L2F_V0:%.*]] : i32, [[L2F_V1:%.*]] : i32):
// CHECK-NEXT:         [[L2F_CMP:%.*]] = "llvm.icmp"([[L2F_V1]], [[L2F_C1]]) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"([[L2F_CMP]]) [^[[BB_L2F_BODY:.*]], ^[[BB_L2F_EXIT:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[BB_L2F_BODY]]():
// CHECK-NEXT:         [[L2F_SHR:%.*]] = "llvm.ashr"([[L2F_V1]], [[L2F_C1]]) : (i32, i32) -> i32
// CHECK-NEXT:         [[L2F_ADD:%.*]] = "llvm.add"([[L2F_V0]], [[L2F_C1]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"([[L2F_ADD]], [[L2F_SHR]]) [^[[BB_L2F_COND]]] : (i32, i32) -> ()
// CHECK-NEXT:       ^[[BB_L2F_EXIT]]():
// CHECK-NEXT:         "llvm.return"([[L2F_V0]]) : (i32) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}}> ({
// CHECK-NEXT:       ^[[BB_BCT:.*]]([[BCT_A0:%.*]] : i32, [[BCT_A1:%.*]] : i32, [[BCT_A2:%.*]] : i32, [[BCT_A3:%.*]] : i32, [[BCT_P0:%.*]] : !llvm.ptr, [[BCT_P1:%.*]] : !llvm.ptr):
// CHECK-NEXT:         [[BCT_M0:%.*]] = "llvm.mul"([[BCT_A2]], [[BCT_A1]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         [[BCT_R0:%.*]] = "llvm.srem"([[BCT_M0]], [[BCT_A3]]) : (i32, i32) -> i32
// CHECK-NEXT:         [[BCT_S0:%.*]] = "llvm.add"([[BCT_A0]], [[BCT_R0]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         [[BCT_R1:%.*]] = "llvm.srem"([[BCT_S0]], [[BCT_A3]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"([[BCT_R1]], [[BCT_P0]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         [[BCT_M1:%.*]] = "llvm.mul"([[BCT_A2]], [[BCT_A1]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         [[BCT_R2:%.*]] = "llvm.srem"([[BCT_M1]], [[BCT_A3]]) : (i32, i32) -> i32
// CHECK-NEXT:         [[BCT_SB:%.*]] = "llvm.sub"([[BCT_A0]], [[BCT_R2]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         [[BCT_AD:%.*]] = "llvm.add"([[BCT_SB]], [[BCT_A3]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         [[BCT_R3:%.*]] = "llvm.srem"([[BCT_AD]], [[BCT_A3]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"([[BCT_R3]], [[BCT_P1]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}}> ({
// CHECK-NEXT:       ^[[BB_BGS:.*]]([[BGS_A0:%.*]] : i32, [[BGS_A1:%.*]] : i32, [[BGS_A2:%.*]] : i32, [[BGS_A3:%.*]] : i32, [[BGS_P0:%.*]] : !llvm.ptr, [[BGS_P1:%.*]] : !llvm.ptr):
// CHECK-NEXT:         [[BGS_S0:%.*]] = "llvm.add"([[BGS_A0]], [[BGS_A1]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         [[BGS_R0:%.*]] = "llvm.srem"([[BGS_S0]], [[BGS_A3]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"([[BGS_R0]], [[BGS_P0]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         [[BGS_SB:%.*]] = "llvm.sub"([[BGS_A0]], [[BGS_A1]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         [[BGS_M0:%.*]] = "llvm.mul"([[BGS_SB]], [[BGS_A2]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         [[BGS_R1:%.*]] = "llvm.srem"([[BGS_M0]], [[BGS_A3]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"([[BGS_R1]], [[BGS_P1]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}}> ({
// CHECK-NEXT:       ^[[BB_NTT:.*]]([[NTT_A0:%.*]] : !llvm.ptr, [[NTT_A1:%.*]] : i32, [[NTT_A2:%.*]] : i32, [[NTT_A3:%.*]] : !llvm.ptr, [[NTT_A4:%.*]] : i32, [[NTT_A5:%.*]] : i32):
// CHECK-NEXT:         [[NTT_C0:%.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         [[NTT_C1:%.*]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// CHECK-NEXT:         [[NTT_C2:%.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         [[NTT_CMP0:%.*]] = "llvm.icmp"([[NTT_A4]], [[NTT_C0]]) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"([[NTT_CMP0]]) [^[[BB_NTT_1:.*]], ^[[BB_NTT_2:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[BB_NTT_1]]():
// CHECK-NEXT:         "llvm.br"([[NTT_A1]]) [^[[BB_NTT_3:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_2]]():
// CHECK-NEXT:         "llvm.br"([[NTT_C1]]) [^[[BB_NTT_3]]] : (i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_3]]([[NTT_V0:%.*]] : i32):
// CHECK-NEXT:         [[NTT_CMP1:%.*]] = "llvm.icmp"([[NTT_A4]], [[NTT_C0]]) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"([[NTT_CMP1]]) [^[[BB_NTT_4:.*]], ^[[BB_NTT_5:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[BB_NTT_4]]():
// CHECK-NEXT:         "llvm.br"([[NTT_C2]]) [^[[BB_NTT_6:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_5]]():
// CHECK-NEXT:         [[NTT_DIV0:%.*]] = "llvm.sdiv"([[NTT_A5]], [[NTT_C1]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"([[NTT_DIV0]]) [^[[BB_NTT_6]]] : (i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_6]]([[NTT_V1:%.*]] : i32):
// CHECK-NEXT:         [[NTT_DIV1:%.*]] = "llvm.sdiv"([[NTT_A1]], [[NTT_C1]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"([[NTT_V0]], [[NTT_V1]], [[NTT_DIV1]], [[NTT_C0]]) [^[[BB_NTT_7:.*]]] : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_7]]([[NTT_V2:%.*]] : i32, [[NTT_V3:%.*]] : i32, [[NTT_V4:%.*]] : i32, [[NTT_V5:%.*]] : i32):
// CHECK-NEXT:         "llvm.br"([[NTT_C0]], [[NTT_A1]]) [^[[BB_NTT_8:.*]]] : (i32, i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_8]]([[NTT_V6:%.*]] : i32, [[NTT_V7:%.*]] : i32):
// CHECK-NEXT:         [[NTT_CMP2:%.*]] = "llvm.icmp"([[NTT_V7]], [[NTT_C2]]) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"([[NTT_CMP2]]) [^[[BB_NTT_9:.*]], ^[[BB_NTT_10:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[BB_NTT_9]]():
// CHECK-NEXT:         [[NTT_SHR0:%.*]] = "llvm.ashr"([[NTT_V7]], [[NTT_C2]]) : (i32, i32) -> i32
// CHECK-NEXT:         [[NTT_ADD0:%.*]] = "llvm.add"([[NTT_V6]], [[NTT_C2]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"([[NTT_ADD0]], [[NTT_SHR0]]) [^[[BB_NTT_8]]] : (i32, i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_10]]():
// CHECK-NEXT:         [[NTT_CMP3:%.*]] = "llvm.icmp"([[NTT_V5]], [[NTT_V6]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"([[NTT_CMP3]]) [^[[BB_NTT_11:.*]], ^[[BB_NTT_12:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[BB_NTT_11]]():
// CHECK-NEXT:         "llvm.br"([[NTT_C0]]) [^[[BB_NTT_13:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_13]]([[NTT_V8:%.*]] : i32):
// CHECK-NEXT:         [[NTT_DIV2:%.*]] = "llvm.sdiv"([[NTT_A1]], [[NTT_V2]]) : (i32, i32) -> i32
// CHECK-NEXT:         [[NTT_CMP4:%.*]] = "llvm.icmp"([[NTT_V8]], [[NTT_DIV2]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"([[NTT_CMP4]]) [^[[BB_NTT_14:.*]], ^[[BB_NTT_15:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[BB_NTT_14]]():
// CHECK-NEXT:         "llvm.br"([[NTT_C0]]) [^[[BB_NTT_16:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_16]]([[NTT_V9:%.*]] : i32):
// CHECK-NEXT:         [[NTT_DIV3:%.*]] = "llvm.sdiv"([[NTT_V2]], [[NTT_C1]]) : (i32, i32) -> i32
// CHECK-NEXT:         [[NTT_CMP5:%.*]] = "llvm.icmp"([[NTT_V9]], [[NTT_DIV3]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"([[NTT_CMP5]]) [^[[BB_NTT_17:.*]], ^[[BB_NTT_18:.*]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[BB_NTT_17]]():
// CHECK:              "llvm.br"() [^[[BB_NTT_19:.*]]] : () -> ()
// CHECK-NEXT:       ^[[BB_NTT_19]]():
// CHECK-NEXT:         [[NTT_ADD1:%.*]] = "llvm.add"([[NTT_V9]], [[NTT_C2]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"([[NTT_ADD1]]) [^[[BB_NTT_16]]] : (i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_18]]():
// CHECK-NEXT:         "llvm.br"() [^[[BB_NTT_20:.*]]] : () -> ()
// CHECK-NEXT:       ^[[BB_NTT_20]]():
// CHECK-NEXT:         [[NTT_ADD2:%.*]] = "llvm.add"([[NTT_V8]], [[NTT_C2]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"([[NTT_ADD2]]) [^[[BB_NTT_13]]] : (i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_15]]():
// CHECK:              "llvm.br"() [^[[BB_NTT_21:.*]]] : () -> ()
// CHECK-NEXT:       ^[[BB_NTT_21]]():
// CHECK-NEXT:         [[NTT_ADD3:%.*]] = "llvm.add"([[NTT_V5]], [[NTT_C2]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"({{.*}}) [^[[BB_NTT_7]]] : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[BB_NTT_12]]():
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: })
