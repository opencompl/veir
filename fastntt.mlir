#loop_annotation = #llvm.loop_annotation<mustProgress = true>
module attributes {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "Ubuntu clang version 18.1.3 (1ubuntu1)", llvm.module_asm = [], llvm.target_triple = "x86_64-pc-linux-gnu"} {
  llvm.module_flags [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]
  llvm.func @log2FloorAux(%arg0: i32 {llvm.noundef}) -> i32 attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(0 : i32) : i32
    %1 = llvm.mlir.constant(1 : i32) : i32
    llvm.br ^bb1(%0, %arg0 : i32, i32)
  ^bb1(%2: i32, %3: i32):  // 2 preds: ^bb0, ^bb2
    %4 = llvm.icmp "sgt" %3, %1 : i32
    llvm.cond_br %4, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %5 = llvm.ashr %3, %1 : i32
    %6 = llvm.add %2, %1 overflow<nsw> : i32
    llvm.br ^bb1(%6, %5 : i32, i32) {loop_annotation = #loop_annotation}
  ^bb3:  // pred: ^bb1
    llvm.return %2 : i32
  }
  llvm.func @log2Floor(%arg0: i32 {llvm.noundef}) -> i32 attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(0 : i32) : i32
    %1 = llvm.mlir.constant(1 : i32) : i32
    llvm.br ^bb1(%0, %arg0 : i32, i32)
  ^bb1(%2: i32, %3: i32):  // 2 preds: ^bb0, ^bb2
    %4 = llvm.icmp "sgt" %3, %1 : i32
    llvm.cond_br %4, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %5 = llvm.ashr %3, %1 : i32
    %6 = llvm.add %2, %1 overflow<nsw> : i32
    llvm.br ^bb1(%6, %5 : i32, i32) {loop_annotation = #loop_annotation}
  ^bb3:  // pred: ^bb1
    llvm.return %2 : i32
  }
  llvm.func @bflyCT(%arg0: i32 {llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: i32 {llvm.noundef}, %arg4: !llvm.ptr {llvm.noundef}, %arg5: !llvm.ptr {llvm.noundef}) attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mul %arg2, %arg1 overflow<nsw> : i32
    %1 = llvm.srem %0, %arg3 : i32
    %2 = llvm.add %arg0, %1 overflow<nsw> : i32
    %3 = llvm.srem %2, %arg3 : i32
    llvm.store %3, %arg4 {alignment = 4 : i64} : i32, !llvm.ptr
    %4 = llvm.mul %arg2, %arg1 overflow<nsw> : i32
    %5 = llvm.srem %4, %arg3 : i32
    %6 = llvm.sub %arg0, %5 overflow<nsw> : i32
    %7 = llvm.add %6, %arg3 overflow<nsw> : i32
    %8 = llvm.srem %7, %arg3 : i32
    llvm.store %8, %arg5 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.return
  }
  llvm.func @bflyGS(%arg0: i32 {llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: i32 {llvm.noundef}, %arg4: !llvm.ptr {llvm.noundef}, %arg5: !llvm.ptr {llvm.noundef}) attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.add %arg0, %arg1 overflow<nsw> : i32
    %1 = llvm.srem %0, %arg3 : i32
    llvm.store %1, %arg4 {alignment = 4 : i64} : i32, !llvm.ptr
    %2 = llvm.sub %arg0, %arg1 overflow<nsw> : i32
    %3 = llvm.mul %2, %arg2 overflow<nsw> : i32
    %4 = llvm.srem %3, %arg3 : i32
    llvm.store %4, %arg5 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.return
  }
  llvm.func @fastNTT(%arg0: !llvm.ptr {llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: !llvm.ptr {llvm.noundef}, %arg4: i32 {llvm.noundef}, %arg5: i32 {llvm.noundef}) attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(0 : i32) : i32
    %1 = llvm.mlir.constant(2 : i32) : i32
    %2 = llvm.mlir.constant(1 : i32) : i32
    %3 = llvm.icmp "ne" %arg4, %0 : i32
    llvm.cond_br %3, ^bb1, ^bb2
  ^bb1:  // pred: ^bb0
    llvm.br ^bb3(%arg1 : i32)
  ^bb2:  // pred: ^bb0
    llvm.br ^bb3(%1 : i32)
  ^bb3(%4: i32):  // 2 preds: ^bb1, ^bb2
    %5 = llvm.icmp "ne" %arg4, %0 : i32
    llvm.cond_br %5, ^bb4, ^bb5
  ^bb4:  // pred: ^bb3
    llvm.br ^bb6(%2 : i32)
  ^bb5:  // pred: ^bb3
    %6 = llvm.sdiv %arg5, %1 : i32
    llvm.br ^bb6(%6 : i32)
  ^bb6(%7: i32):  // 2 preds: ^bb4, ^bb5
    %8 = llvm.sdiv %arg1, %1 : i32
    llvm.br ^bb7(%4, %7, %8, %0 : i32, i32, i32, i32)
  ^bb7(%9: i32, %10: i32, %11: i32, %12: i32):  // 2 preds: ^bb6, ^bb26
    llvm.br ^bb8(%0, %arg1 : i32, i32)
  ^bb8(%13: i32, %14: i32):  // 2 preds: ^bb7, ^bb9
    %15 = llvm.icmp "sgt" %14, %2 : i32
    llvm.cond_br %15, ^bb9, ^bb10
  ^bb9:  // pred: ^bb8
    %16 = llvm.ashr %14, %2 : i32
    %17 = llvm.add %13, %2 overflow<nsw> : i32
    llvm.br ^bb8(%17, %16 : i32, i32) {loop_annotation = #loop_annotation}
  ^bb10:  // pred: ^bb8
    %18 = llvm.icmp "slt" %12, %13 : i32
    llvm.cond_br %18, ^bb11, ^bb27
  ^bb11:  // pred: ^bb10
    llvm.br ^bb12(%0 : i32)
  ^bb12(%19: i32):  // 2 preds: ^bb11, ^bb18
    %20 = llvm.sdiv %arg1, %9 : i32
    %21 = llvm.icmp "slt" %19, %20 : i32
    llvm.cond_br %21, ^bb13, ^bb19
  ^bb13:  // pred: ^bb12
    llvm.br ^bb14(%0 : i32)
  ^bb14(%22: i32):  // 2 preds: ^bb13, ^bb16
    %23 = llvm.sdiv %9, %1 : i32
    %24 = llvm.icmp "slt" %22, %23 : i32
    llvm.cond_br %24, ^bb15, ^bb17
  ^bb15:  // pred: ^bb14
    %25 = llvm.mul %19, %9 overflow<nsw> : i32
    %26 = llvm.add %25, %22 overflow<nsw> : i32
    %27 = llvm.sext %26 : i32 to i64
    %28 = llvm.getelementptr inbounds %arg0[%27] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %29 = llvm.load %28 {alignment = 4 : i64} : !llvm.ptr -> i32
    %30 = llvm.mul %19, %9 overflow<nsw> : i32
    %31 = llvm.add %30, %22 overflow<nsw> : i32
    %32 = llvm.sdiv %9, %1 : i32
    %33 = llvm.add %31, %32 overflow<nsw> : i32
    %34 = llvm.sext %33 : i32 to i64
    %35 = llvm.getelementptr inbounds %arg0[%34] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %36 = llvm.load %35 {alignment = 4 : i64} : !llvm.ptr -> i32
    %37 = llvm.mul %1, %22 overflow<nsw> : i32
    %38 = llvm.add %37, %2 overflow<nsw> : i32
    %39 = llvm.mul %38, %11 overflow<nsw> : i32
    %40 = llvm.sext %39 : i32 to i64
    %41 = llvm.getelementptr inbounds %arg3[%40] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %42 = llvm.load %41 {alignment = 4 : i64} : !llvm.ptr -> i32
    %43 = llvm.mul %42, %36 overflow<nsw> : i32
    %44 = llvm.srem %43, %arg2 : i32
    %45 = llvm.add %29, %44 overflow<nsw> : i32
    %46 = llvm.srem %45, %arg2 : i32
    %47 = llvm.mul %42, %36 overflow<nsw> : i32
    %48 = llvm.srem %47, %arg2 : i32
    %49 = llvm.sub %29, %48 overflow<nsw> : i32
    %50 = llvm.add %49, %arg2 overflow<nsw> : i32
    %51 = llvm.srem %50, %arg2 : i32
    %52 = llvm.mul %19, %9 overflow<nsw> : i32
    %53 = llvm.add %52, %22 overflow<nsw> : i32
    %54 = llvm.sext %53 : i32 to i64
    %55 = llvm.getelementptr inbounds %arg0[%54] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %46, %55 {alignment = 4 : i64} : i32, !llvm.ptr
    %56 = llvm.mul %19, %9 overflow<nsw> : i32
    %57 = llvm.add %56, %22 overflow<nsw> : i32
    %58 = llvm.sdiv %9, %1 : i32
    %59 = llvm.add %57, %58 overflow<nsw> : i32
    %60 = llvm.sext %59 : i32 to i64
    %61 = llvm.getelementptr inbounds %arg0[%60] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %51, %61 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb16
  ^bb16:  // pred: ^bb15
    %62 = llvm.add %22, %2 overflow<nsw> : i32
    llvm.br ^bb14(%62 : i32) {loop_annotation = #loop_annotation}
  ^bb17:  // pred: ^bb14
    llvm.br ^bb18
  ^bb18:  // pred: ^bb17
    %63 = llvm.add %19, %2 overflow<nsw> : i32
    llvm.br ^bb12(%63 : i32) {loop_annotation = #loop_annotation}
  ^bb19:  // pred: ^bb12
    %64 = llvm.sdiv %11, %1 : i32
    %65 = llvm.icmp "ne" %arg4, %0 : i32
    llvm.cond_br %65, ^bb20, ^bb21
  ^bb20:  // pred: ^bb19
    %66 = llvm.sdiv %9, %1 : i32
    llvm.br ^bb22(%66 : i32)
  ^bb21:  // pred: ^bb19
    %67 = llvm.mul %9, %1 overflow<nsw> : i32
    llvm.br ^bb22(%67 : i32)
  ^bb22(%68: i32):  // 2 preds: ^bb20, ^bb21
    %69 = llvm.icmp "ne" %arg4, %0 : i32
    llvm.cond_br %69, ^bb23, ^bb24
  ^bb23:  // pred: ^bb22
    %70 = llvm.mul %10, %1 overflow<nsw> : i32
    llvm.br ^bb25(%70 : i32)
  ^bb24:  // pred: ^bb22
    %71 = llvm.sdiv %10, %1 : i32
    llvm.br ^bb25(%71 : i32)
  ^bb25(%72: i32):  // 2 preds: ^bb23, ^bb24
    llvm.br ^bb26
  ^bb26:  // pred: ^bb25
    %73 = llvm.add %12, %2 overflow<nsw> : i32
    llvm.br ^bb7(%68, %72, %64, %73 : i32, i32, i32, i32) {loop_annotation = #loop_annotation}
  ^bb27:  // pred: ^bb10
    llvm.return
  }
}
