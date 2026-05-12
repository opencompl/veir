// RUN: veir-opt %s | filecheck %s

// This test results from the lowering of a C implementation of the FastNTT algorithm, based on the Heir 
// pseudocode: https://github.com/google/heir/blob/1210ad37dc9531d6e60d8ddbce81dbd79f7626a6/lib/Dialect/Polynomial/Conversions/PolynomialToModArith/PolynomialToModArith.cpp#L1060. 
// We detail the flags and specifics of the lowering from C to LLVM IR in https://github.com/opencompl/veir/pull/458

"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "log2FloorAux", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg19: i32):
    %95 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %96 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.br"(%95, %arg19)[^bb1] : (i32, i32) -> ()
  ^bb1(%97: i32, %98: i32):  // 2 preds: ^bb0, ^bb2
    %99 = "llvm.icmp"(%98, %96) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%99)[^bb2, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %100 = "llvm.ashr"(%98, %96) : (i32, i32) -> i32
    %101 = "llvm.add"(%97, %96) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%101, %100)[^bb1] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i32, i32) -> ()
  ^bb3:  // pred: ^bb1
    "llvm.return"(%97) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "log2Floor", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg18: i32):
    %88 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %89 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.br"(%88, %arg18)[^bb1] : (i32, i32) -> ()
  ^bb1(%90: i32, %91: i32):  // 2 preds: ^bb0, ^bb2
    %92 = "llvm.icmp"(%91, %89) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%92)[^bb2, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %93 = "llvm.ashr"(%91, %89) : (i32, i32) -> i32
    %94 = "llvm.add"(%90, %89) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%94, %93)[^bb1] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i32, i32) -> ()
  ^bb3:  // pred: ^bb1
    "llvm.return"(%90) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (i32, i32, i32, i32, ptr, ptr)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "bflyCT", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg12: i32, %arg13: i32, %arg14: i32, %arg15: i32, %arg16: !llvm.ptr, %arg17: !llvm.ptr):
    %79 = "llvm.mul"(%arg14, %arg13) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %80 = "llvm.srem"(%79, %arg15) : (i32, i32) -> i32
    %81 = "llvm.add"(%arg12, %80) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %82 = "llvm.srem"(%81, %arg15) : (i32, i32) -> i32
    "llvm.store"(%82, %arg16) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %83 = "llvm.mul"(%arg14, %arg13) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %84 = "llvm.srem"(%83, %arg15) : (i32, i32) -> i32
    %85 = "llvm.sub"(%arg12, %84) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %86 = "llvm.add"(%85, %arg15) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %87 = "llvm.srem"(%86, %arg15) : (i32, i32) -> i32
    "llvm.store"(%87, %arg17) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (i32, i32, i32, i32, ptr, ptr)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "bflyGS", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg6: i32, %arg7: i32, %arg8: i32, %arg9: i32, %arg10: !llvm.ptr, %arg11: !llvm.ptr):
    %74 = "llvm.add"(%arg6, %arg7) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %75 = "llvm.srem"(%74, %arg9) : (i32, i32) -> i32
    "llvm.store"(%75, %arg10) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %76 = "llvm.sub"(%arg6, %arg7) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %77 = "llvm.mul"(%76, %arg8) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %78 = "llvm.srem"(%77, %arg9) : (i32, i32) -> i32
    "llvm.store"(%78, %arg11) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, always_inline, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (ptr, i32, i32, ptr, i32, i32)>, linkage = #llvm.linkage<external>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "fastNTT", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: i32, %arg2: i32, %arg3: !llvm.ptr, %arg4: i32, %arg5: i32):
    %0 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %3 = "llvm.icmp"(%arg4, %0) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%3)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    "llvm.br"(%arg1)[^bb3] : (i32) -> ()
  ^bb2:  // pred: ^bb0
    "llvm.br"(%1)[^bb3] : (i32) -> ()
  ^bb3(%4: i32):  // 2 preds: ^bb1, ^bb2
    %5 = "llvm.icmp"(%arg4, %0) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%5)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    "llvm.br"(%2)[^bb6] : (i32) -> ()
  ^bb5:  // pred: ^bb3
    %6 = "llvm.sdiv"(%arg5, %1) : (i32, i32) -> i32
    "llvm.br"(%6)[^bb6] : (i32) -> ()
  ^bb6(%7: i32):  // 2 preds: ^bb4, ^bb5
    %8 = "llvm.sdiv"(%arg1, %1) : (i32, i32) -> i32
    "llvm.br"(%4, %7, %8, %0)[^bb7] : (i32, i32, i32, i32) -> ()
  ^bb7(%9: i32, %10: i32, %11: i32, %12: i32):  // 2 preds: ^bb6, ^bb26
    "llvm.br"(%0, %arg1)[^bb8] : (i32, i32) -> ()
  ^bb8(%13: i32, %14: i32):  // 2 preds: ^bb7, ^bb9
    %15 = "llvm.icmp"(%14, %2) <{predicate = 4 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%15)[^bb9, ^bb10] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb9:  // pred: ^bb8
    %16 = "llvm.ashr"(%14, %2) : (i32, i32) -> i32
    %17 = "llvm.add"(%13, %2) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%17, %16)[^bb8] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i32, i32) -> ()
  ^bb10:  // pred: ^bb8
    %18 = "llvm.icmp"(%12, %13) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%18)[^bb11, ^bb27] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb11:  // pred: ^bb10
    "llvm.br"(%0)[^bb12] : (i32) -> ()
  ^bb12(%19: i32):  // 2 preds: ^bb11, ^bb18
    %20 = "llvm.sdiv"(%arg1, %9) : (i32, i32) -> i32
    %21 = "llvm.icmp"(%19, %20) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%21)[^bb13, ^bb19] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb13:  // pred: ^bb12
    "llvm.br"(%0)[^bb14] : (i32) -> ()
  ^bb14(%22: i32):  // 2 preds: ^bb13, ^bb16
    %23 = "llvm.sdiv"(%9, %1) : (i32, i32) -> i32
    %24 = "llvm.icmp"(%22, %23) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%24)[^bb15, ^bb17] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb15:  // pred: ^bb14
    %25 = "llvm.mul"(%19, %9) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %26 = "llvm.add"(%25, %22) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %27 = "llvm.sext"(%26) : (i32) -> i64
    %28 = "llvm.getelementptr"(%arg0, %27) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %29 = "llvm.load"(%28) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %30 = "llvm.mul"(%19, %9) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %31 = "llvm.add"(%30, %22) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %32 = "llvm.sdiv"(%9, %1) : (i32, i32) -> i32
    %33 = "llvm.add"(%31, %32) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %34 = "llvm.sext"(%33) : (i32) -> i64
    %35 = "llvm.getelementptr"(%arg0, %34) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %36 = "llvm.load"(%35) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %37 = "llvm.mul"(%1, %22) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %38 = "llvm.add"(%37, %2) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %39 = "llvm.mul"(%38, %11) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %40 = "llvm.sext"(%39) : (i32) -> i64
    %41 = "llvm.getelementptr"(%arg3, %40) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %42 = "llvm.load"(%41) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %43 = "llvm.mul"(%42, %36) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %44 = "llvm.srem"(%43, %arg2) : (i32, i32) -> i32
    %45 = "llvm.add"(%29, %44) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %46 = "llvm.srem"(%45, %arg2) : (i32, i32) -> i32
    %47 = "llvm.mul"(%42, %36) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %48 = "llvm.srem"(%47, %arg2) : (i32, i32) -> i32
    %49 = "llvm.sub"(%29, %48) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %50 = "llvm.add"(%49, %arg2) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %51 = "llvm.srem"(%50, %arg2) : (i32, i32) -> i32
    %52 = "llvm.mul"(%19, %9) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %53 = "llvm.add"(%52, %22) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %54 = "llvm.sext"(%53) : (i32) -> i64
    %55 = "llvm.getelementptr"(%arg0, %54) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%46, %55) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %56 = "llvm.mul"(%19, %9) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %57 = "llvm.add"(%56, %22) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %58 = "llvm.sdiv"(%9, %1) : (i32, i32) -> i32
    %59 = "llvm.add"(%57, %58) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %60 = "llvm.sext"(%59) : (i32) -> i64
    %61 = "llvm.getelementptr"(%arg0, %60) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%51, %61) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb16] : () -> ()
  ^bb16:  // pred: ^bb15
    %62 = "llvm.add"(%22, %2) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%62)[^bb14] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i32) -> ()
  ^bb17:  // pred: ^bb14
    "llvm.br"()[^bb18] : () -> ()
  ^bb18:  // pred: ^bb17
    %63 = "llvm.add"(%19, %2) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%63)[^bb12] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i32) -> ()
  ^bb19:  // pred: ^bb12
    %64 = "llvm.sdiv"(%11, %1) : (i32, i32) -> i32
    %65 = "llvm.icmp"(%arg4, %0) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%65)[^bb20, ^bb21] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb20:  // pred: ^bb19
    %66 = "llvm.sdiv"(%9, %1) : (i32, i32) -> i32
    "llvm.br"(%66)[^bb22] : (i32) -> ()
  ^bb21:  // pred: ^bb19
    %67 = "llvm.mul"(%9, %1) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%67)[^bb22] : (i32) -> ()
  ^bb22(%68: i32):  // 2 preds: ^bb20, ^bb21
    %69 = "llvm.icmp"(%arg4, %0) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%69)[^bb23, ^bb24] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb23:  // pred: ^bb22
    %70 = "llvm.mul"(%10, %1) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%70)[^bb25] : (i32) -> ()
  ^bb24:  // pred: ^bb22
    %71 = "llvm.sdiv"(%10, %1) : (i32, i32) -> i32
    "llvm.br"(%71)[^bb25] : (i32) -> ()
  ^bb25(%72: i32):  // 2 preds: ^bb23, ^bb24
    "llvm.br"()[^bb26] : () -> ()
  ^bb26:  // pred: ^bb25
    %73 = "llvm.add"(%12, %2) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%68, %72, %64, %73)[^bb7] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>}> : (i32, i32, i32, i32) -> ()
  ^bb27:  // pred: ^bb10
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "Ubuntu clang version 18.1.3 (1ubuntu1)", llvm.module_asm = [], llvm.target_triple = "x86_64-pc-linux-gnu"} : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "builtin.unregistered"() : () -> ()
// CHECK-NEXT:     "builtin.unregistered"() ({
// CHECK-NEXT:       ^7(%arg7_0 : i32):
// CHECK-NEXT:         %8 = "builtin.unregistered"() : () -> i32
// CHECK-NEXT:         %9 = "builtin.unregistered"() : () -> i32
// CHECK-NEXT:         "llvm.br"(%8, %arg7_0) [^10] : (i32, i32) -> ()
// CHECK-NEXT:       ^10(%arg10_0 : i32, %arg10_1 : i32):
// CHECK-NEXT:         %12 = "llvm.icmp"(%arg10_1, %9) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%12) [^13, ^14] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^13():
// CHECK-NEXT:         %16 = "llvm.ashr"(%arg10_1, %9) : (i32, i32) -> i32
// CHECK-NEXT:         %17 = "llvm.add"(%arg10_0, %9) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%17, %16) [^10] : (i32, i32) -> ()
// CHECK-NEXT:       ^14():
// CHECK-NEXT:         "llvm.return"(%arg10_0) : (i32) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "builtin.unregistered"() ({
// CHECK-NEXT:       ^22(%arg22_0 : i32):
// CHECK-NEXT:         %23 = "builtin.unregistered"() : () -> i32
// CHECK-NEXT:         %24 = "builtin.unregistered"() : () -> i32
// CHECK-NEXT:         "llvm.br"(%23, %arg22_0) [^25] : (i32, i32) -> ()
// CHECK-NEXT:       ^25(%arg25_0 : i32, %arg25_1 : i32):
// CHECK-NEXT:         %27 = "llvm.icmp"(%arg25_1, %24) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%27) [^28, ^29] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^28():
// CHECK-NEXT:         %31 = "llvm.ashr"(%arg25_1, %24) : (i32, i32) -> i32
// CHECK-NEXT:         %32 = "llvm.add"(%arg25_0, %24) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%32, %31) [^25] : (i32, i32) -> ()
// CHECK-NEXT:       ^29():
// CHECK-NEXT:         "llvm.return"(%arg25_0) : (i32) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "builtin.unregistered"() ({
// CHECK-NEXT:       ^37(%arg37_0 : i32, %arg37_1 : i32, %arg37_2 : i32, %arg37_3 : i32, %arg37_4 : !llvm.ptr, %arg37_5 : !llvm.ptr):
// CHECK-NEXT:         %38 = "llvm.mul"(%arg37_2, %arg37_1) : (i32, i32) -> i32
// CHECK-NEXT:         %39 = "llvm.srem"(%38, %arg37_3) : (i32, i32) -> i32
// CHECK-NEXT:         %40 = "llvm.add"(%arg37_0, %39) : (i32, i32) -> i32
// CHECK-NEXT:         %41 = "llvm.srem"(%40, %arg37_3) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%41, %arg37_4) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %43 = "llvm.mul"(%arg37_2, %arg37_1) : (i32, i32) -> i32
// CHECK-NEXT:         %44 = "llvm.srem"(%43, %arg37_3) : (i32, i32) -> i32
// CHECK-NEXT:         %45 = "llvm.sub"(%arg37_0, %44) : (i32, i32) -> i32
// CHECK-NEXT:         %46 = "llvm.add"(%45, %arg37_3) : (i32, i32) -> i32
// CHECK-NEXT:         %47 = "llvm.srem"(%46, %arg37_3) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%47, %arg37_5) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "builtin.unregistered"() ({
// CHECK-NEXT:       ^52(%arg52_0 : i32, %arg52_1 : i32, %arg52_2 : i32, %arg52_3 : i32, %arg52_4 : !llvm.ptr, %arg52_5 : !llvm.ptr):
// CHECK-NEXT:         %53 = "llvm.add"(%arg52_0, %arg52_1) : (i32, i32) -> i32
// CHECK-NEXT:         %54 = "llvm.srem"(%53, %arg52_3) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%54, %arg52_4) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %56 = "llvm.sub"(%arg52_0, %arg52_1) : (i32, i32) -> i32
// CHECK-NEXT:         %57 = "llvm.mul"(%56, %arg52_2) : (i32, i32) -> i32
// CHECK-NEXT:         %58 = "llvm.srem"(%57, %arg52_3) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%58, %arg52_5) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "builtin.unregistered"() ({
// CHECK-NEXT:       ^63(%arg63_0 : !llvm.ptr, %arg63_1 : i32, %arg63_2 : i32, %arg63_3 : !llvm.ptr, %arg63_4 : i32, %arg63_5 : i32):
// CHECK-NEXT:         %64 = "builtin.unregistered"() : () -> i32
// CHECK-NEXT:         %65 = "builtin.unregistered"() : () -> i32
// CHECK-NEXT:         %66 = "builtin.unregistered"() : () -> i32
// CHECK-NEXT:         %67 = "llvm.icmp"(%arg63_4, %64) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%67) [^68, ^69] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^68():
// CHECK-NEXT:         "llvm.br"(%arg63_1) [^71] : (i32) -> ()
// CHECK-NEXT:       ^69():
// CHECK-NEXT:         "llvm.br"(%65) [^71] : (i32) -> ()
// CHECK-NEXT:       ^71(%arg71_0 : i32):
// CHECK-NEXT:         %74 = "llvm.icmp"(%arg63_4, %64) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%74) [^75, ^76] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^75():
// CHECK-NEXT:         "llvm.br"(%66) [^78] : (i32) -> ()
// CHECK-NEXT:       ^76():
// CHECK-NEXT:         %80 = "llvm.sdiv"(%arg63_5, %65) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%80) [^78] : (i32) -> ()
// CHECK-NEXT:       ^78(%arg78_0 : i32):
// CHECK-NEXT:         %82 = "llvm.sdiv"(%arg63_1, %65) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%arg71_0, %arg78_0, %82, %64) [^83] : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^83(%arg83_0 : i32, %arg83_1 : i32, %arg83_2 : i32, %arg83_3 : i32):
// CHECK-NEXT:         "llvm.br"(%64, %arg63_1) [^85] : (i32, i32) -> ()
// CHECK-NEXT:       ^85(%arg85_0 : i32, %arg85_1 : i32):
// CHECK-NEXT:         %87 = "llvm.icmp"(%arg85_1, %66) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%87) [^88, ^89] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^88():
// CHECK-NEXT:         %91 = "llvm.ashr"(%arg85_1, %66) : (i32, i32) -> i32
// CHECK-NEXT:         %92 = "llvm.add"(%arg85_0, %66) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%92, %91) [^85] : (i32, i32) -> ()
// CHECK-NEXT:       ^89():
// CHECK-NEXT:         %94 = "llvm.icmp"(%arg83_3, %arg85_0) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%94) [^95, ^96] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^95():
// CHECK-NEXT:         "llvm.br"(%64) [^98] : (i32) -> ()
// CHECK-NEXT:       ^98(%arg98_0 : i32):
// CHECK-NEXT:         %100 = "llvm.sdiv"(%arg63_1, %arg83_0) : (i32, i32) -> i32
// CHECK-NEXT:         %101 = "llvm.icmp"(%arg98_0, %100) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%101) [^102, ^103] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^102():
// CHECK-NEXT:         "llvm.br"(%64) [^105] : (i32) -> ()
// CHECK-NEXT:       ^105(%arg105_0 : i32):
// CHECK-NEXT:         %107 = "llvm.sdiv"(%arg83_0, %65) : (i32, i32) -> i32
// CHECK-NEXT:         %108 = "llvm.icmp"(%arg105_0, %107) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%108) [^109, ^110] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^109():
// CHECK-NEXT:         %112 = "llvm.mul"(%arg98_0, %arg83_0) : (i32, i32) -> i32
// CHECK-NEXT:         %113 = "llvm.add"(%112, %arg105_0) : (i32, i32) -> i32
// CHECK-NEXT:         %114 = "llvm.sext"(%113) : (i32) -> i64
// CHECK-NEXT:         %115 = "llvm.getelementptr"(%arg63_0, %114) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %116 = "llvm.load"(%115) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %117 = "llvm.mul"(%arg98_0, %arg83_0) : (i32, i32) -> i32
// CHECK-NEXT:         %118 = "llvm.add"(%117, %arg105_0) : (i32, i32) -> i32
// CHECK-NEXT:         %119 = "llvm.sdiv"(%arg83_0, %65) : (i32, i32) -> i32
// CHECK-NEXT:         %120 = "llvm.add"(%118, %119) : (i32, i32) -> i32
// CHECK-NEXT:         %121 = "llvm.sext"(%120) : (i32) -> i64
// CHECK-NEXT:         %122 = "llvm.getelementptr"(%arg63_0, %121) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %123 = "llvm.load"(%122) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %124 = "llvm.mul"(%65, %arg105_0) : (i32, i32) -> i32
// CHECK-NEXT:         %125 = "llvm.add"(%124, %66) : (i32, i32) -> i32
// CHECK-NEXT:         %126 = "llvm.mul"(%125, %arg83_2) : (i32, i32) -> i32
// CHECK-NEXT:         %127 = "llvm.sext"(%126) : (i32) -> i64
// CHECK-NEXT:         %128 = "llvm.getelementptr"(%arg63_3, %127) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %129 = "llvm.load"(%128) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %130 = "llvm.mul"(%129, %123) : (i32, i32) -> i32
// CHECK-NEXT:         %131 = "llvm.srem"(%130, %arg63_2) : (i32, i32) -> i32
// CHECK-NEXT:         %132 = "llvm.add"(%116, %131) : (i32, i32) -> i32
// CHECK-NEXT:         %133 = "llvm.srem"(%132, %arg63_2) : (i32, i32) -> i32
// CHECK-NEXT:         %134 = "llvm.mul"(%129, %123) : (i32, i32) -> i32
// CHECK-NEXT:         %135 = "llvm.srem"(%134, %arg63_2) : (i32, i32) -> i32
// CHECK-NEXT:         %136 = "llvm.sub"(%116, %135) : (i32, i32) -> i32
// CHECK-NEXT:         %137 = "llvm.add"(%136, %arg63_2) : (i32, i32) -> i32
// CHECK-NEXT:         %138 = "llvm.srem"(%137, %arg63_2) : (i32, i32) -> i32
// CHECK-NEXT:         %139 = "llvm.mul"(%arg98_0, %arg83_0) : (i32, i32) -> i32
// CHECK-NEXT:         %140 = "llvm.add"(%139, %arg105_0) : (i32, i32) -> i32
// CHECK-NEXT:         %141 = "llvm.sext"(%140) : (i32) -> i64
// CHECK-NEXT:         %142 = "llvm.getelementptr"(%arg63_0, %141) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%133, %142) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %144 = "llvm.mul"(%arg98_0, %arg83_0) : (i32, i32) -> i32
// CHECK-NEXT:         %145 = "llvm.add"(%144, %arg105_0) : (i32, i32) -> i32
// CHECK-NEXT:         %146 = "llvm.sdiv"(%arg83_0, %65) : (i32, i32) -> i32
// CHECK-NEXT:         %147 = "llvm.add"(%145, %146) : (i32, i32) -> i32
// CHECK-NEXT:         %148 = "llvm.sext"(%147) : (i32) -> i64
// CHECK-NEXT:         %149 = "llvm.getelementptr"(%arg63_0, %148) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%138, %149) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^151] : () -> ()
// CHECK-NEXT:       ^151():
// CHECK-NEXT:         %153 = "llvm.add"(%arg105_0, %66) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%153) [^105] : (i32) -> ()
// CHECK-NEXT:       ^110():
// CHECK-NEXT:         "llvm.br"() [^155] : () -> ()
// CHECK-NEXT:       ^155():
// CHECK-NEXT:         %157 = "llvm.add"(%arg98_0, %66) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%157) [^98] : (i32) -> ()
// CHECK-NEXT:       ^103():
// CHECK-NEXT:         %159 = "llvm.sdiv"(%arg83_2, %65) : (i32, i32) -> i32
// CHECK-NEXT:         %160 = "llvm.icmp"(%arg63_4, %64) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%160) [^161, ^162] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^161():
// CHECK-NEXT:         %164 = "llvm.sdiv"(%arg83_0, %65) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%164) [^165] : (i32) -> ()
// CHECK-NEXT:       ^162():
// CHECK-NEXT:         %167 = "llvm.mul"(%arg83_0, %65) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%167) [^165] : (i32) -> ()
// CHECK-NEXT:       ^165(%arg165_0 : i32):
// CHECK-NEXT:         %169 = "llvm.icmp"(%arg63_4, %64) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%169) [^170, ^171] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^170():
// CHECK-NEXT:         %173 = "llvm.mul"(%arg83_1, %65) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%173) [^174] : (i32) -> ()
// CHECK-NEXT:       ^171():
// CHECK-NEXT:         %176 = "llvm.sdiv"(%arg83_1, %65) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%176) [^174] : (i32) -> ()
// CHECK-NEXT:       ^174(%arg174_0 : i32):
// CHECK-NEXT:         "llvm.br"() [^178] : () -> ()
// CHECK-NEXT:       ^178():
// CHECK-NEXT:         %180 = "llvm.add"(%arg83_3, %66) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%arg165_0, %arg174_0, %159, %180) [^83] : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^96():
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, "llvm.ident" = "Ubuntu clang version 18.1.3 (1ubuntu1)", "llvm.module_asm" = [], "llvm.target_triple" = "x86_64-pc-linux-gnu"} : () -> ()
