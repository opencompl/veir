#loop_annotation = #llvm.loop_annotation<mustProgress = true>
module attributes {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "Ubuntu clang version 18.1.3 (1ubuntu1)", llvm.module_asm = [], llvm.target_triple = "x86_64-pc-linux-gnu"} {
  llvm.module_flags [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]
  llvm.func @log2FloorAux(%arg0: i32 {llvm.noundef}) -> i32 attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.mlir.constant(0 : i32) : i32
    %2 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %3 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    llvm.store %arg0, %2 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %1, %3 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb1
  ^bb1:  // 2 preds: ^bb0, ^bb2
    %4 = llvm.load %2 {alignment = 4 : i64} : !llvm.ptr -> i32
    %5 = llvm.icmp "sgt" %4, %0 : i32
    llvm.cond_br %5, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %6 = llvm.load %2 {alignment = 4 : i64} : !llvm.ptr -> i32
    %7 = llvm.ashr %6, %0 : i32
    llvm.store %7, %2 {alignment = 4 : i64} : i32, !llvm.ptr
    %8 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    %9 = llvm.add %8, %0 overflow<nsw> : i32
    llvm.store %9, %3 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb1 {loop_annotation = #loop_annotation}
  ^bb3:  // pred: ^bb1
    %10 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.return %10 : i32
  }
  llvm.func @log2Floor(%arg0: i32 {llvm.noundef}) -> i32 attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.mlir.constant(0 : i32) : i32
    %2 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %3 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %4 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    llvm.store %arg0, %4 {alignment = 4 : i64} : i32, !llvm.ptr
    %5 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %5, %2 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %1, %3 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb1
  ^bb1:  // 2 preds: ^bb0, ^bb2
    %6 = llvm.load %2 {alignment = 4 : i64} : !llvm.ptr -> i32
    %7 = llvm.icmp "sgt" %6, %0 : i32
    llvm.cond_br %7, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %8 = llvm.load %2 {alignment = 4 : i64} : !llvm.ptr -> i32
    %9 = llvm.ashr %8, %0 : i32
    llvm.store %9, %2 {alignment = 4 : i64} : i32, !llvm.ptr
    %10 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    %11 = llvm.add %10, %0 overflow<nsw> : i32
    llvm.store %11, %3 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb1 {loop_annotation = #loop_annotation}
  ^bb3:  // pred: ^bb1
    %12 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.return %12 : i32
  }
  llvm.func @bflyCT(%arg0: i32 {llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: i32 {llvm.noundef}, %arg4: !llvm.ptr {llvm.noundef}, %arg5: !llvm.ptr {llvm.noundef}) attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %2 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %3 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %4 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %5 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %6 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    llvm.store %arg0, %1 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg1, %2 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg2, %3 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg3, %4 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg4, %5 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    llvm.store %arg5, %6 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    %7 = llvm.load %1 {alignment = 4 : i64} : !llvm.ptr -> i32
    %8 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    %9 = llvm.load %2 {alignment = 4 : i64} : !llvm.ptr -> i32
    %10 = llvm.mul %8, %9 overflow<nsw> : i32
    %11 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %12 = llvm.srem %10, %11 : i32
    %13 = llvm.add %7, %12 overflow<nsw> : i32
    %14 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %15 = llvm.srem %13, %14 : i32
    %16 = llvm.load %5 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    llvm.store %15, %16 {alignment = 4 : i64} : i32, !llvm.ptr
    %17 = llvm.load %1 {alignment = 4 : i64} : !llvm.ptr -> i32
    %18 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    %19 = llvm.load %2 {alignment = 4 : i64} : !llvm.ptr -> i32
    %20 = llvm.mul %18, %19 overflow<nsw> : i32
    %21 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %22 = llvm.srem %20, %21 : i32
    %23 = llvm.sub %17, %22 overflow<nsw> : i32
    %24 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %25 = llvm.add %23, %24 overflow<nsw> : i32
    %26 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %27 = llvm.srem %25, %26 : i32
    %28 = llvm.load %6 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    llvm.store %27, %28 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.return
  }
  llvm.func @bflyGS(%arg0: i32 {llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: i32 {llvm.noundef}, %arg4: !llvm.ptr {llvm.noundef}, %arg5: !llvm.ptr {llvm.noundef}) attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %2 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %3 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %4 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %5 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %6 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    llvm.store %arg0, %1 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg1, %2 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg2, %3 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg3, %4 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg4, %5 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    llvm.store %arg5, %6 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    %7 = llvm.load %1 {alignment = 4 : i64} : !llvm.ptr -> i32
    %8 = llvm.load %2 {alignment = 4 : i64} : !llvm.ptr -> i32
    %9 = llvm.add %7, %8 overflow<nsw> : i32
    %10 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %11 = llvm.srem %9, %10 : i32
    %12 = llvm.load %5 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    llvm.store %11, %12 {alignment = 4 : i64} : i32, !llvm.ptr
    %13 = llvm.load %1 {alignment = 4 : i64} : !llvm.ptr -> i32
    %14 = llvm.load %2 {alignment = 4 : i64} : !llvm.ptr -> i32
    %15 = llvm.sub %13, %14 overflow<nsw> : i32
    %16 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    %17 = llvm.mul %15, %16 overflow<nsw> : i32
    %18 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %19 = llvm.srem %17, %18 : i32
    %20 = llvm.load %6 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    llvm.store %19, %20 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.return
  }
  llvm.func @fastNTT(%arg0: !llvm.ptr {llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: !llvm.ptr {llvm.noundef}, %arg4: i32 {llvm.noundef}, %arg5: i32 {llvm.noundef}) attributes {always_inline, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_unwind, passthrough = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.mlir.constant(0 : i32) : i32
    %2 = llvm.mlir.constant(2 : i32) : i32
    %3 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %4 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %5 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %6 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %7 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %8 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %9 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %10 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %11 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %12 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %13 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %14 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %15 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %16 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %17 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %18 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %19 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %20 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %21 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %22 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %23 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %24 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %25 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %26 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %27 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %28 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    llvm.store %arg0, %12 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    llvm.store %arg1, %13 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg2, %14 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg3, %15 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    llvm.store %arg4, %16 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg5, %17 {alignment = 4 : i64} : i32, !llvm.ptr
    %29 = llvm.load %16 {alignment = 4 : i64} : !llvm.ptr -> i32
    %30 = llvm.icmp "ne" %29, %1 : i32
    llvm.cond_br %30, ^bb1, ^bb2
  ^bb1:  // pred: ^bb0
    %31 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.br ^bb3(%31 : i32)
  ^bb2:  // pred: ^bb0
    llvm.br ^bb3(%2 : i32)
  ^bb3(%32: i32):  // 2 preds: ^bb1, ^bb2
    llvm.store %32, %18 {alignment = 4 : i64} : i32, !llvm.ptr
    %33 = llvm.load %16 {alignment = 4 : i64} : !llvm.ptr -> i32
    %34 = llvm.icmp "ne" %33, %1 : i32
    llvm.cond_br %34, ^bb4, ^bb5
  ^bb4:  // pred: ^bb3
    llvm.br ^bb6(%0 : i32)
  ^bb5:  // pred: ^bb3
    %35 = llvm.load %17 {alignment = 4 : i64} : !llvm.ptr -> i32
    %36 = llvm.sdiv %35, %2 : i32
    llvm.br ^bb6(%36 : i32)
  ^bb6(%37: i32):  // 2 preds: ^bb4, ^bb5
    llvm.store %37, %19 {alignment = 4 : i64} : i32, !llvm.ptr
    %38 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %39 = llvm.sdiv %38, %2 : i32
    llvm.store %39, %20 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %1, %21 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb7
  ^bb7:  // 2 preds: ^bb6, ^bb26
    %40 = llvm.load %21 {alignment = 4 : i64} : !llvm.ptr -> i32
    %41 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %41, %11 {alignment = 4 : i64} : i32, !llvm.ptr
    %42 = llvm.load %11 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %42, %9 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %1, %10 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb8
  ^bb8:  // 2 preds: ^bb7, ^bb9
    %43 = llvm.load %9 {alignment = 4 : i64} : !llvm.ptr -> i32
    %44 = llvm.icmp "sgt" %43, %0 : i32
    llvm.cond_br %44, ^bb9, ^bb10
  ^bb9:  // pred: ^bb8
    %45 = llvm.load %9 {alignment = 4 : i64} : !llvm.ptr -> i32
    %46 = llvm.ashr %45, %0 : i32
    llvm.store %46, %9 {alignment = 4 : i64} : i32, !llvm.ptr
    %47 = llvm.load %10 {alignment = 4 : i64} : !llvm.ptr -> i32
    %48 = llvm.add %47, %0 overflow<nsw> : i32
    llvm.store %48, %10 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb8 {loop_annotation = #loop_annotation}
  ^bb10:  // pred: ^bb8
    %49 = llvm.load %10 {alignment = 4 : i64} : !llvm.ptr -> i32
    %50 = llvm.icmp "slt" %40, %49 : i32
    llvm.cond_br %50, ^bb11, ^bb27
  ^bb11:  // pred: ^bb10
    llvm.store %1, %22 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb12
  ^bb12:  // 2 preds: ^bb11, ^bb18
    %51 = llvm.load %22 {alignment = 4 : i64} : !llvm.ptr -> i32
    %52 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %53 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %54 = llvm.sdiv %52, %53 : i32
    %55 = llvm.icmp "slt" %51, %54 : i32
    llvm.cond_br %55, ^bb13, ^bb19
  ^bb13:  // pred: ^bb12
    llvm.store %1, %23 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb14
  ^bb14:  // 2 preds: ^bb13, ^bb16
    %56 = llvm.load %23 {alignment = 4 : i64} : !llvm.ptr -> i32
    %57 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %58 = llvm.sdiv %57, %2 : i32
    %59 = llvm.icmp "slt" %56, %58 : i32
    llvm.cond_br %59, ^bb15, ^bb17
  ^bb15:  // pred: ^bb14
    %60 = llvm.load %12 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %61 = llvm.load %22 {alignment = 4 : i64} : !llvm.ptr -> i32
    %62 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %63 = llvm.mul %61, %62 overflow<nsw> : i32
    %64 = llvm.load %23 {alignment = 4 : i64} : !llvm.ptr -> i32
    %65 = llvm.add %63, %64 overflow<nsw> : i32
    %66 = llvm.sext %65 : i32 to i64
    %67 = llvm.getelementptr inbounds %60[%66] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %68 = llvm.load %67 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %68, %24 {alignment = 4 : i64} : i32, !llvm.ptr
    %69 = llvm.load %12 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %70 = llvm.load %22 {alignment = 4 : i64} : !llvm.ptr -> i32
    %71 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %72 = llvm.mul %70, %71 overflow<nsw> : i32
    %73 = llvm.load %23 {alignment = 4 : i64} : !llvm.ptr -> i32
    %74 = llvm.add %72, %73 overflow<nsw> : i32
    %75 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %76 = llvm.sdiv %75, %2 : i32
    %77 = llvm.add %74, %76 overflow<nsw> : i32
    %78 = llvm.sext %77 : i32 to i64
    %79 = llvm.getelementptr inbounds %69[%78] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %80 = llvm.load %79 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %80, %25 {alignment = 4 : i64} : i32, !llvm.ptr
    %81 = llvm.load %15 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %82 = llvm.load %23 {alignment = 4 : i64} : !llvm.ptr -> i32
    %83 = llvm.mul %2, %82 overflow<nsw> : i32
    %84 = llvm.add %83, %0 overflow<nsw> : i32
    %85 = llvm.load %20 {alignment = 4 : i64} : !llvm.ptr -> i32
    %86 = llvm.mul %84, %85 overflow<nsw> : i32
    %87 = llvm.sext %86 : i32 to i64
    %88 = llvm.getelementptr inbounds %81[%87] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %89 = llvm.load %88 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %89, %26 {alignment = 4 : i64} : i32, !llvm.ptr
    %90 = llvm.load %24 {alignment = 4 : i64} : !llvm.ptr -> i32
    %91 = llvm.load %25 {alignment = 4 : i64} : !llvm.ptr -> i32
    %92 = llvm.load %26 {alignment = 4 : i64} : !llvm.ptr -> i32
    %93 = llvm.load %14 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %90, %3 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %91, %4 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %92, %5 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %93, %6 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %27, %7 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    llvm.store %28, %8 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    %94 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    %95 = llvm.load %5 {alignment = 4 : i64} : !llvm.ptr -> i32
    %96 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %97 = llvm.mul %95, %96 overflow<nsw> : i32
    %98 = llvm.load %6 {alignment = 4 : i64} : !llvm.ptr -> i32
    %99 = llvm.srem %97, %98 : i32
    %100 = llvm.add %94, %99 overflow<nsw> : i32
    %101 = llvm.load %6 {alignment = 4 : i64} : !llvm.ptr -> i32
    %102 = llvm.srem %100, %101 : i32
    %103 = llvm.load %7 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    llvm.store %102, %103 {alignment = 4 : i64} : i32, !llvm.ptr
    %104 = llvm.load %3 {alignment = 4 : i64} : !llvm.ptr -> i32
    %105 = llvm.load %5 {alignment = 4 : i64} : !llvm.ptr -> i32
    %106 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %107 = llvm.mul %105, %106 overflow<nsw> : i32
    %108 = llvm.load %6 {alignment = 4 : i64} : !llvm.ptr -> i32
    %109 = llvm.srem %107, %108 : i32
    %110 = llvm.sub %104, %109 overflow<nsw> : i32
    %111 = llvm.load %6 {alignment = 4 : i64} : !llvm.ptr -> i32
    %112 = llvm.add %110, %111 overflow<nsw> : i32
    %113 = llvm.load %6 {alignment = 4 : i64} : !llvm.ptr -> i32
    %114 = llvm.srem %112, %113 : i32
    %115 = llvm.load %8 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    llvm.store %114, %115 {alignment = 4 : i64} : i32, !llvm.ptr
    %116 = llvm.load %27 {alignment = 4 : i64} : !llvm.ptr -> i32
    %117 = llvm.load %12 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %118 = llvm.load %22 {alignment = 4 : i64} : !llvm.ptr -> i32
    %119 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %120 = llvm.mul %118, %119 overflow<nsw> : i32
    %121 = llvm.load %23 {alignment = 4 : i64} : !llvm.ptr -> i32
    %122 = llvm.add %120, %121 overflow<nsw> : i32
    %123 = llvm.sext %122 : i32 to i64
    %124 = llvm.getelementptr inbounds %117[%123] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %116, %124 {alignment = 4 : i64} : i32, !llvm.ptr
    %125 = llvm.load %28 {alignment = 4 : i64} : !llvm.ptr -> i32
    %126 = llvm.load %12 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %127 = llvm.load %22 {alignment = 4 : i64} : !llvm.ptr -> i32
    %128 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %129 = llvm.mul %127, %128 overflow<nsw> : i32
    %130 = llvm.load %23 {alignment = 4 : i64} : !llvm.ptr -> i32
    %131 = llvm.add %129, %130 overflow<nsw> : i32
    %132 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %133 = llvm.sdiv %132, %2 : i32
    %134 = llvm.add %131, %133 overflow<nsw> : i32
    %135 = llvm.sext %134 : i32 to i64
    %136 = llvm.getelementptr inbounds %126[%135] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %125, %136 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb16
  ^bb16:  // pred: ^bb15
    %137 = llvm.load %23 {alignment = 4 : i64} : !llvm.ptr -> i32
    %138 = llvm.add %137, %0 overflow<nsw> : i32
    llvm.store %138, %23 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb14 {loop_annotation = #loop_annotation}
  ^bb17:  // pred: ^bb14
    llvm.br ^bb18
  ^bb18:  // pred: ^bb17
    %139 = llvm.load %22 {alignment = 4 : i64} : !llvm.ptr -> i32
    %140 = llvm.add %139, %0 overflow<nsw> : i32
    llvm.store %140, %22 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb12 {loop_annotation = #loop_annotation}
  ^bb19:  // pred: ^bb12
    %141 = llvm.load %20 {alignment = 4 : i64} : !llvm.ptr -> i32
    %142 = llvm.sdiv %141, %2 : i32
    llvm.store %142, %20 {alignment = 4 : i64} : i32, !llvm.ptr
    %143 = llvm.load %16 {alignment = 4 : i64} : !llvm.ptr -> i32
    %144 = llvm.icmp "ne" %143, %1 : i32
    llvm.cond_br %144, ^bb20, ^bb21
  ^bb20:  // pred: ^bb19
    %145 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %146 = llvm.sdiv %145, %2 : i32
    llvm.br ^bb22(%146 : i32)
  ^bb21:  // pred: ^bb19
    %147 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %148 = llvm.mul %147, %2 overflow<nsw> : i32
    llvm.br ^bb22(%148 : i32)
  ^bb22(%149: i32):  // 2 preds: ^bb20, ^bb21
    llvm.store %149, %18 {alignment = 4 : i64} : i32, !llvm.ptr
    %150 = llvm.load %16 {alignment = 4 : i64} : !llvm.ptr -> i32
    %151 = llvm.icmp "ne" %150, %1 : i32
    llvm.cond_br %151, ^bb23, ^bb24
  ^bb23:  // pred: ^bb22
    %152 = llvm.load %19 {alignment = 4 : i64} : !llvm.ptr -> i32
    %153 = llvm.mul %152, %2 overflow<nsw> : i32
    llvm.br ^bb25(%153 : i32)
  ^bb24:  // pred: ^bb22
    %154 = llvm.load %19 {alignment = 4 : i64} : !llvm.ptr -> i32
    %155 = llvm.sdiv %154, %2 : i32
    llvm.br ^bb25(%155 : i32)
  ^bb25(%156: i32):  // 2 preds: ^bb23, ^bb24
    llvm.store %156, %19 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb26
  ^bb26:  // pred: ^bb25
    %157 = llvm.load %21 {alignment = 4 : i64} : !llvm.ptr -> i32
    %158 = llvm.add %157, %0 overflow<nsw> : i32
    llvm.store %158, %21 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb7 {loop_annotation = #loop_annotation}
  ^bb27:  // pred: ^bb10
    llvm.return
  }
}
