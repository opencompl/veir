"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<i64 (i64)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "log2FloorAux", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg19: i64):
    %90 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %91 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    "llvm.br"(%90, %arg19)[^bb1] : (i64, i64) -> ()
  ^bb1(%92: i64, %93: i64):  // 2 preds: ^bb0, ^bb2
    %94 = "llvm.icmp"(%93, %91) <{predicate = 4 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%94)[^bb2, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %95 = "llvm.ashr"(%93, %91) : (i64, i64) -> i64
    %96 = "llvm.add"(%92, %91) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.br"(%96, %95)[^bb1] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i64, i64) -> ()
  ^bb3:  // pred: ^bb1
    "llvm.return"(%92) : (i64) -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<i64 (i64)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "log2Floor", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg18: i64):
    %83 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %84 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    "llvm.br"(%83, %arg18)[^bb1] : (i64, i64) -> ()
  ^bb1(%85: i64, %86: i64):  // 2 preds: ^bb0, ^bb2
    %87 = "llvm.icmp"(%86, %84) <{predicate = 4 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%87)[^bb2, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %88 = "llvm.ashr"(%86, %84) : (i64, i64) -> i64
    %89 = "llvm.add"(%85, %84) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.br"(%89, %88)[^bb1] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i64, i64) -> ()
  ^bb3:  // pred: ^bb1
    "llvm.return"(%85) : (i64) -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (i64, i64, i64, i64, ptr, ptr)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "bflyCT", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg12: i64, %arg13: i64, %arg14: i64, %arg15: i64, %arg16: !llvm.ptr, %arg17: !llvm.ptr):
    %74 = "llvm.mul"(%arg14, %arg13) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %75 = "llvm.srem"(%74, %arg15) : (i64, i64) -> i64
    %76 = "llvm.add"(%arg12, %75) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %77 = "llvm.srem"(%76, %arg15) : (i64, i64) -> i64
    "llvm.store"(%77, %arg16) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %78 = "llvm.mul"(%arg14, %arg13) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %79 = "llvm.srem"(%78, %arg15) : (i64, i64) -> i64
    %80 = "llvm.sub"(%arg12, %79) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %81 = "llvm.add"(%80, %arg15) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %82 = "llvm.srem"(%81, %arg15) : (i64, i64) -> i64
    "llvm.store"(%82, %arg17) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (i64, i64, i64, i64, ptr, ptr)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "bflyGS", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg6: i64, %arg7: i64, %arg8: i64, %arg9: i64, %arg10: !llvm.ptr, %arg11: !llvm.ptr):
    %69 = "llvm.add"(%arg6, %arg7) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %70 = "llvm.srem"(%69, %arg9) : (i64, i64) -> i64
    "llvm.store"(%70, %arg10) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %71 = "llvm.sub"(%arg6, %arg7) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %72 = "llvm.mul"(%71, %arg8) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %73 = "llvm.srem"(%72, %arg9) : (i64, i64) -> i64
    "llvm.store"(%73, %arg11) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
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