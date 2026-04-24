#loop_annotation = #llvm.loop_annotation<mustProgress = true>
"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (i32, i32, i32, i32, ptr, ptr)>, linkage = #llvm.linkage<external>, no_inline, no_unwind, optimize_none, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "bflyCT", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 0 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg11: i32, %arg12: i32, %arg13: i32, %arg14: i32, %arg15: !llvm.ptr, %arg16: !llvm.ptr):
    %141 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %142 = "llvm.alloca"(%141) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %143 = "llvm.alloca"(%141) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %144 = "llvm.alloca"(%141) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %145 = "llvm.alloca"(%141) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %146 = "llvm.alloca"(%141) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
    %147 = "llvm.alloca"(%141) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
    "llvm.store"(%arg11, %142) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg12, %143) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg13, %144) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg14, %145) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg15, %146) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.store"(%arg16, %147) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    %148 = "llvm.load"(%142) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %149 = "llvm.load"(%144) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %150 = "llvm.load"(%143) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %151 = "llvm.mul"(%149, %150) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %152 = "llvm.load"(%145) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %153 = "llvm.srem"(%151, %152) : (i32, i32) -> i32
    %154 = "llvm.add"(%148, %153) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %155 = "llvm.load"(%145) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %156 = "llvm.srem"(%154, %155) : (i32, i32) -> i32
    %157 = "llvm.load"(%146) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%156, %157) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %158 = "llvm.load"(%142) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %159 = "llvm.load"(%144) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %160 = "llvm.load"(%143) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %161 = "llvm.mul"(%159, %160) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %162 = "llvm.load"(%145) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %163 = "llvm.srem"(%161, %162) : (i32, i32) -> i32
    %164 = "llvm.sub"(%158, %163) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %165 = "llvm.load"(%145) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %166 = "llvm.add"(%164, %165) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %167 = "llvm.load"(%145) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %168 = "llvm.srem"(%166, %167) : (i32, i32) -> i32
    %169 = "llvm.load"(%147) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%168, %169) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (i32, i32, i32, i32, ptr, ptr)>, linkage = #llvm.linkage<external>, no_inline, no_unwind, optimize_none, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "bflyGS", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 0 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg5: i32, %arg6: i32, %arg7: i32, %arg8: i32, %arg9: !llvm.ptr, %arg10: !llvm.ptr):
    %120 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %121 = "llvm.alloca"(%120) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %122 = "llvm.alloca"(%120) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %123 = "llvm.alloca"(%120) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %124 = "llvm.alloca"(%120) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %125 = "llvm.alloca"(%120) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
    %126 = "llvm.alloca"(%120) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
    "llvm.store"(%arg5, %121) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg6, %122) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg7, %123) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg8, %124) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg9, %125) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.store"(%arg10, %126) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    %127 = "llvm.load"(%121) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %128 = "llvm.load"(%122) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %129 = "llvm.add"(%127, %128) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %130 = "llvm.load"(%124) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %131 = "llvm.srem"(%129, %130) : (i32, i32) -> i32
    %132 = "llvm.load"(%125) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%131, %132) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %133 = "llvm.load"(%121) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %134 = "llvm.load"(%122) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %135 = "llvm.sub"(%133, %134) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %136 = "llvm.load"(%123) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %137 = "llvm.mul"(%135, %136) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %138 = "llvm.load"(%124) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %139 = "llvm.srem"(%137, %138) : (i32, i32) -> i32
    %140 = "llvm.load"(%126) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%139, %140) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, frame_pointer = #llvm.framePointerKind<all>, function_type = !llvm.func<void (ptr, i32, i32, ptr, i32)>, linkage = #llvm.linkage<external>, no_inline, no_unwind, optimize_none, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], sym_name = "fastNTT", target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", unnamed_addr = 0 : i64, uwtable_kind = #llvm.uwtableKind<async>, visibility_ = 0 : i64}> ({
  ^bb0(%arg0: !llvm.ptr, %arg1: i32, %arg2: i32, %arg3: !llvm.ptr, %arg4: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %3 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
    %4 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %5 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %6 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
    %7 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %8 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %9 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %10 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %11 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %12 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %13 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %14 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %15 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %16 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %17 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    %18 = "llvm.alloca"(%0) <{alignment = 4 : i64, elem_type = i32}> : (i32) -> !llvm.ptr
    "llvm.store"(%arg0, %3) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.store"(%arg1, %4) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg2, %5) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%arg3, %6) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.store"(%arg4, %7) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %19 = "llvm.load"(%7) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %20 = "llvm.icmp"(%19, %1) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%20)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    %21 = "llvm.load"(%4) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    "llvm.br"(%21)[^bb3] : (i32) -> ()
  ^bb2:  // pred: ^bb0
    "llvm.br"(%2)[^bb3] : (i32) -> ()
  ^bb3(%22: i32):  // 2 preds: ^bb1, ^bb2
    "llvm.store"(%22, %8) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %23 = "llvm.load"(%7) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %24 = "llvm.icmp"(%23, %1) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%24)[^bb4, ^bb5] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    "llvm.br"(%0)[^bb6] : (i32) -> ()
  ^bb5:  // pred: ^bb3
    %25 = "llvm.load"(%4) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %26 = "llvm.sdiv"(%25, %2) : (i32, i32) -> i32
    "llvm.br"(%26)[^bb6] : (i32) -> ()
  ^bb6(%27: i32):  // 2 preds: ^bb4, ^bb5
    "llvm.store"(%27, %9) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %28 = "llvm.load"(%4) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %29 = "llvm.sdiv"(%28, %2) : (i32, i32) -> i32
    "llvm.store"(%29, %10) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%1, %11) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb7] : () -> ()
  ^bb7:  // 2 preds: ^bb6, ^bb23
    %30 = "llvm.load"(%11) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %31 = "llvm.load"(%4) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %32 = "llvm.intr.cttz"(%31) <{is_zero_poison = true}> : (i32) -> i32
    %33 = "llvm.icmp"(%30, %32) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%33)[^bb8, ^bb24] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb8:  // pred: ^bb7
    "llvm.store"(%1, %12) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb9] : () -> ()
  ^bb9:  // 2 preds: ^bb8, ^bb15
    %34 = "llvm.load"(%12) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %35 = "llvm.load"(%4) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %36 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %37 = "llvm.sdiv"(%35, %36) : (i32, i32) -> i32
    %38 = "llvm.icmp"(%34, %37) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%38)[^bb10, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb10:  // pred: ^bb9
    "llvm.store"(%1, %13) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb11] : () -> ()
  ^bb11:  // 2 preds: ^bb10, ^bb13
    %39 = "llvm.load"(%13) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %40 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %41 = "llvm.sdiv"(%40, %2) : (i32, i32) -> i32
    %42 = "llvm.icmp"(%39, %41) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%42)[^bb12, ^bb14] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb12:  // pred: ^bb11
    %43 = "llvm.load"(%3) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %44 = "llvm.load"(%12) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %45 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %46 = "llvm.mul"(%44, %45) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %47 = "llvm.load"(%13) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %48 = "llvm.add"(%46, %47) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %49 = "llvm.sext"(%48) : (i32) -> i64
    %50 = "llvm.getelementptr"(%43, %49) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %51 = "llvm.load"(%50) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    "llvm.store"(%51, %14) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %52 = "llvm.load"(%3) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %53 = "llvm.load"(%12) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %54 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %55 = "llvm.mul"(%53, %54) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %56 = "llvm.load"(%13) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %57 = "llvm.add"(%55, %56) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %58 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %59 = "llvm.sdiv"(%58, %2) : (i32, i32) -> i32
    %60 = "llvm.add"(%57, %59) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %61 = "llvm.sext"(%60) : (i32) -> i64
    %62 = "llvm.getelementptr"(%52, %61) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %63 = "llvm.load"(%62) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    "llvm.store"(%63, %15) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %64 = "llvm.load"(%6) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %65 = "llvm.load"(%13) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %66 = "llvm.mul"(%2, %65) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %67 = "llvm.add"(%66, %0) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %68 = "llvm.load"(%10) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %69 = "llvm.mul"(%67, %68) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %70 = "llvm.sext"(%69) : (i32) -> i64
    %71 = "llvm.getelementptr"(%64, %70) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %72 = "llvm.load"(%71) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    "llvm.store"(%72, %16) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %73 = "llvm.load"(%14) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %74 = "llvm.load"(%15) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %75 = "llvm.load"(%16) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %76 = "llvm.load"(%5) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    "llvm.call"(%73, %74, %75, %76, %17, %18) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @bflyCT, fastmathFlags = #llvm.fastmath<none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 6, 0>}> : (i32, i32, i32, i32, !llvm.ptr, !llvm.ptr) -> ()
    %77 = "llvm.load"(%17) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %78 = "llvm.load"(%3) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %79 = "llvm.load"(%12) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %80 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %81 = "llvm.mul"(%79, %80) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %82 = "llvm.load"(%13) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %83 = "llvm.add"(%81, %82) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %84 = "llvm.sext"(%83) : (i32) -> i64
    %85 = "llvm.getelementptr"(%78, %84) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%77, %85) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %86 = "llvm.load"(%18) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %87 = "llvm.load"(%3) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %88 = "llvm.load"(%12) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %89 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %90 = "llvm.mul"(%88, %89) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %91 = "llvm.load"(%13) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %92 = "llvm.add"(%90, %91) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %93 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %94 = "llvm.sdiv"(%93, %2) : (i32, i32) -> i32
    %95 = "llvm.add"(%92, %94) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %96 = "llvm.sext"(%95) : (i32) -> i64
    %97 = "llvm.getelementptr"(%87, %96) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%86, %97) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb13] : () -> ()
  ^bb13:  // pred: ^bb12
    %98 = "llvm.load"(%13) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %99 = "llvm.add"(%98, %0) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.store"(%99, %13) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb11] <{loop_annotation = #loop_annotation}> : () -> ()
  ^bb14:  // pred: ^bb11
    "llvm.br"()[^bb15] : () -> ()
  ^bb15:  // pred: ^bb14
    %100 = "llvm.load"(%12) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %101 = "llvm.add"(%100, %0) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.store"(%101, %12) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb9] <{loop_annotation = #loop_annotation}> : () -> ()
  ^bb16:  // pred: ^bb9
    %102 = "llvm.load"(%10) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %103 = "llvm.sdiv"(%102, %2) : (i32, i32) -> i32
    "llvm.store"(%103, %10) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %104 = "llvm.load"(%7) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %105 = "llvm.icmp"(%104, %1) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%105)[^bb17, ^bb18] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb17:  // pred: ^bb16
    %106 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %107 = "llvm.sdiv"(%106, %2) : (i32, i32) -> i32
    "llvm.br"(%107)[^bb19] : (i32) -> ()
  ^bb18:  // pred: ^bb16
    %108 = "llvm.load"(%8) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %109 = "llvm.mul"(%108, %2) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%109)[^bb19] : (i32) -> ()
  ^bb19(%110: i32):  // 2 preds: ^bb17, ^bb18
    "llvm.store"(%110, %8) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    %111 = "llvm.load"(%7) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %112 = "llvm.icmp"(%111, %1) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%112)[^bb20, ^bb21] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb20:  // pred: ^bb19
    %113 = "llvm.load"(%9) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %114 = "llvm.mul"(%113, %2) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.br"(%114)[^bb22] : (i32) -> ()
  ^bb21:  // pred: ^bb19
    %115 = "llvm.load"(%9) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %116 = "llvm.sdiv"(%115, %2) : (i32, i32) -> i32
    "llvm.br"(%116)[^bb22] : (i32) -> ()
  ^bb22(%117: i32):  // 2 preds: ^bb20, ^bb21
    "llvm.store"(%117, %9) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb23] : () -> ()
  ^bb23:  // pred: ^bb22
    %118 = "llvm.load"(%11) <{alignment = 4 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %119 = "llvm.add"(%118, %0) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    "llvm.store"(%119, %11) <{alignment = 4 : i64, ordering = 0 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.br"()[^bb7] <{loop_annotation = #loop_annotation}> : () -> ()
  ^bb24:  // pred: ^bb7
    "llvm.return"() : () -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "Ubuntu clang version 18.1.3 (1ubuntu1)", llvm.module_asm = [], llvm.target_triple = "x86_64-pc-linux-gnu"} : () -> ()

