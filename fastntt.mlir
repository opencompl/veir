#loop_annotation = #llvm.loop_annotation<mustProgress = true>
module attributes {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, llvm.ident = "Ubuntu clang version 18.1.3 (1ubuntu1)", llvm.module_asm = [], llvm.target_triple = "x86_64-pc-linux-gnu"} {
  llvm.comdat @__llvm_global_comdat {
    llvm.comdat_selector @_ZNSt6vectorIiSaIiEEixEm any
    llvm.comdat_selector @_ZNKSt6vectorIiSaIiEEixEm any
  }
  llvm.module_flags [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]
  llvm.func @_Z6bflyCTiiiiRiS_(%arg0: i32 {llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: i32 {llvm.noundef}, %arg4: !llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}, %arg5: !llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}) attributes {dso_local, frame_pointer = #llvm.framePointerKind<all>, no_inline, no_unwind, optimize_none, passthrough = ["mustprogress", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
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
  llvm.func @_Z6bflyGSiiiiRiS_(%arg0: i32 {llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: i32 {llvm.noundef}, %arg4: !llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}, %arg5: !llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}) attributes {dso_local, frame_pointer = #llvm.framePointerKind<all>, no_inline, no_unwind, optimize_none, passthrough = ["mustprogress", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
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
  llvm.func @_Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b(%arg0: !llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, %arg1: i32 {llvm.noundef}, %arg2: i32 {llvm.noundef}, %arg3: !llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, %arg4: i1 {llvm.noundef, llvm.zeroext}) attributes {dso_local, frame_pointer = #llvm.framePointerKind<all>, no_inline, no_unwind, optimize_none, passthrough = ["mustprogress", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.mlir.constant(2 : i32) : i32
    %2 = llvm.mlir.constant(0 : i32) : i32
    %3 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %4 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %5 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %6 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %7 = llvm.alloca %0 x i8 {alignment = 1 : i64} : (i32) -> !llvm.ptr
    %8 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %9 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %10 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %11 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %12 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %13 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %14 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %15 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %16 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %17 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    %18 = llvm.alloca %0 x i32 {alignment = 4 : i64} : (i32) -> !llvm.ptr
    llvm.store %arg0, %3 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    llvm.store %arg1, %4 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg2, %5 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %arg3, %6 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    %19 = llvm.zext %arg4 : i1 to i8
    llvm.store %19, %7 {alignment = 1 : i64} : i8, !llvm.ptr
    %20 = llvm.load %7 {alignment = 1 : i64} : !llvm.ptr -> i8
    %21 = llvm.trunc %20 : i8 to i1
    llvm.cond_br %21, ^bb1, ^bb2
  ^bb1:  // pred: ^bb0
    %22 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.br ^bb3(%22 : i32)
  ^bb2:  // pred: ^bb0
    llvm.br ^bb3(%1 : i32)
  ^bb3(%23: i32):  // 2 preds: ^bb1, ^bb2
    llvm.store %23, %8 {alignment = 4 : i64} : i32, !llvm.ptr
    %24 = llvm.load %7 {alignment = 1 : i64} : !llvm.ptr -> i8
    %25 = llvm.trunc %24 : i8 to i1
    llvm.cond_br %25, ^bb4, ^bb5
  ^bb4:  // pred: ^bb3
    llvm.br ^bb6(%0 : i32)
  ^bb5:  // pred: ^bb3
    %26 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %27 = llvm.sdiv %26, %1 : i32
    llvm.br ^bb6(%27 : i32)
  ^bb6(%28: i32):  // 2 preds: ^bb4, ^bb5
    llvm.store %28, %9 {alignment = 4 : i64} : i32, !llvm.ptr
    %29 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %30 = llvm.sdiv %29, %1 : i32
    llvm.store %30, %10 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.store %2, %11 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb7
  ^bb7:  // 2 preds: ^bb6, ^bb23
    %31 = llvm.load %11 {alignment = 4 : i64} : !llvm.ptr -> i32
    %32 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %33 = "llvm.intr.cttz"(%32) <{is_zero_poison = true}> : (i32) -> i32
    %34 = llvm.icmp "slt" %31, %33 : i32
    llvm.cond_br %34, ^bb8, ^bb24
  ^bb8:  // pred: ^bb7
    llvm.store %2, %12 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb9
  ^bb9:  // 2 preds: ^bb8, ^bb15
    %35 = llvm.load %12 {alignment = 4 : i64} : !llvm.ptr -> i32
    %36 = llvm.load %4 {alignment = 4 : i64} : !llvm.ptr -> i32
    %37 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %38 = llvm.sdiv %36, %37 : i32
    %39 = llvm.icmp "slt" %35, %38 : i32
    llvm.cond_br %39, ^bb10, ^bb16
  ^bb10:  // pred: ^bb9
    llvm.store %2, %13 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb11
  ^bb11:  // 2 preds: ^bb10, ^bb13
    %40 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %41 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %42 = llvm.sdiv %41, %1 : i32
    %43 = llvm.icmp "slt" %40, %42 : i32
    llvm.cond_br %43, ^bb12, ^bb14
  ^bb12:  // pred: ^bb11
    %44 = llvm.load %3 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %45 = llvm.load %12 {alignment = 4 : i64} : !llvm.ptr -> i32
    %46 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %47 = llvm.mul %45, %46 overflow<nsw> : i32
    %48 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %49 = llvm.add %47, %48 overflow<nsw> : i32
    %50 = llvm.sext %49 : i32 to i64
    %51 = llvm.call @_ZNSt6vectorIiSaIiEEixEm(%44, %50) {no_unwind} : (!llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, i64 {llvm.noundef}) -> (!llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef})
    %52 = llvm.load %51 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %52, %14 {alignment = 4 : i64} : i32, !llvm.ptr
    %53 = llvm.load %3 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %54 = llvm.load %12 {alignment = 4 : i64} : !llvm.ptr -> i32
    %55 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %56 = llvm.mul %54, %55 overflow<nsw> : i32
    %57 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %58 = llvm.add %56, %57 overflow<nsw> : i32
    %59 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %60 = llvm.sdiv %59, %1 : i32
    %61 = llvm.add %58, %60 overflow<nsw> : i32
    %62 = llvm.sext %61 : i32 to i64
    %63 = llvm.call @_ZNSt6vectorIiSaIiEEixEm(%53, %62) {no_unwind} : (!llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, i64 {llvm.noundef}) -> (!llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef})
    %64 = llvm.load %63 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %64, %15 {alignment = 4 : i64} : i32, !llvm.ptr
    %65 = llvm.load %6 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %66 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %67 = llvm.mul %1, %66 overflow<nsw> : i32
    %68 = llvm.add %67, %0 overflow<nsw> : i32
    %69 = llvm.load %10 {alignment = 4 : i64} : !llvm.ptr -> i32
    %70 = llvm.mul %68, %69 overflow<nsw> : i32
    %71 = llvm.sext %70 : i32 to i64
    %72 = llvm.call @_ZNKSt6vectorIiSaIiEEixEm(%65, %71) {no_unwind} : (!llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, i64 {llvm.noundef}) -> (!llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef})
    %73 = llvm.load %72 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.store %73, %16 {alignment = 4 : i64} : i32, !llvm.ptr
    %74 = llvm.load %14 {alignment = 4 : i64} : !llvm.ptr -> i32
    %75 = llvm.load %15 {alignment = 4 : i64} : !llvm.ptr -> i32
    %76 = llvm.load %16 {alignment = 4 : i64} : !llvm.ptr -> i32
    %77 = llvm.load %5 {alignment = 4 : i64} : !llvm.ptr -> i32
    llvm.call @_Z6bflyCTiiiiRiS_(%74, %75, %76, %77, %17, %18) : (i32 {llvm.noundef}, i32 {llvm.noundef}, i32 {llvm.noundef}, i32 {llvm.noundef}, !llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}, !llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}) -> ()
    %78 = llvm.load %17 {alignment = 4 : i64} : !llvm.ptr -> i32
    %79 = llvm.load %3 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %80 = llvm.load %12 {alignment = 4 : i64} : !llvm.ptr -> i32
    %81 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %82 = llvm.mul %80, %81 overflow<nsw> : i32
    %83 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %84 = llvm.add %82, %83 overflow<nsw> : i32
    %85 = llvm.sext %84 : i32 to i64
    %86 = llvm.call @_ZNSt6vectorIiSaIiEEixEm(%79, %85) {no_unwind} : (!llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, i64 {llvm.noundef}) -> (!llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef})
    llvm.store %78, %86 {alignment = 4 : i64} : i32, !llvm.ptr
    %87 = llvm.load %18 {alignment = 4 : i64} : !llvm.ptr -> i32
    %88 = llvm.load %3 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %89 = llvm.load %12 {alignment = 4 : i64} : !llvm.ptr -> i32
    %90 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %91 = llvm.mul %89, %90 overflow<nsw> : i32
    %92 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %93 = llvm.add %91, %92 overflow<nsw> : i32
    %94 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %95 = llvm.sdiv %94, %1 : i32
    %96 = llvm.add %93, %95 overflow<nsw> : i32
    %97 = llvm.sext %96 : i32 to i64
    %98 = llvm.call @_ZNSt6vectorIiSaIiEEixEm(%88, %97) {no_unwind} : (!llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, i64 {llvm.noundef}) -> (!llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef})
    llvm.store %87, %98 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb13
  ^bb13:  // pred: ^bb12
    %99 = llvm.load %13 {alignment = 4 : i64} : !llvm.ptr -> i32
    %100 = llvm.add %99, %0 overflow<nsw> : i32
    llvm.store %100, %13 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb11 {loop_annotation = #loop_annotation}
  ^bb14:  // pred: ^bb11
    llvm.br ^bb15
  ^bb15:  // pred: ^bb14
    %101 = llvm.load %12 {alignment = 4 : i64} : !llvm.ptr -> i32
    %102 = llvm.add %101, %0 overflow<nsw> : i32
    llvm.store %102, %12 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb9 {loop_annotation = #loop_annotation}
  ^bb16:  // pred: ^bb9
    %103 = llvm.load %10 {alignment = 4 : i64} : !llvm.ptr -> i32
    %104 = llvm.sdiv %103, %1 : i32
    llvm.store %104, %10 {alignment = 4 : i64} : i32, !llvm.ptr
    %105 = llvm.load %7 {alignment = 1 : i64} : !llvm.ptr -> i8
    %106 = llvm.trunc %105 : i8 to i1
    llvm.cond_br %106, ^bb17, ^bb18
  ^bb17:  // pred: ^bb16
    %107 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %108 = llvm.sdiv %107, %1 : i32
    llvm.br ^bb19(%108 : i32)
  ^bb18:  // pred: ^bb16
    %109 = llvm.load %8 {alignment = 4 : i64} : !llvm.ptr -> i32
    %110 = llvm.mul %109, %1 overflow<nsw> : i32
    llvm.br ^bb19(%110 : i32)
  ^bb19(%111: i32):  // 2 preds: ^bb17, ^bb18
    llvm.store %111, %8 {alignment = 4 : i64} : i32, !llvm.ptr
    %112 = llvm.load %7 {alignment = 1 : i64} : !llvm.ptr -> i8
    %113 = llvm.trunc %112 : i8 to i1
    llvm.cond_br %113, ^bb20, ^bb21
  ^bb20:  // pred: ^bb19
    %114 = llvm.load %9 {alignment = 4 : i64} : !llvm.ptr -> i32
    %115 = llvm.mul %114, %1 overflow<nsw> : i32
    llvm.br ^bb22(%115 : i32)
  ^bb21:  // pred: ^bb19
    %116 = llvm.load %9 {alignment = 4 : i64} : !llvm.ptr -> i32
    %117 = llvm.sdiv %116, %1 : i32
    llvm.br ^bb22(%117 : i32)
  ^bb22(%118: i32):  // 2 preds: ^bb20, ^bb21
    llvm.store %118, %9 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb23
  ^bb23:  // pred: ^bb22
    %119 = llvm.load %11 {alignment = 4 : i64} : !llvm.ptr -> i32
    %120 = llvm.add %119, %0 overflow<nsw> : i32
    llvm.store %120, %11 {alignment = 4 : i64} : i32, !llvm.ptr
    llvm.br ^bb7 {loop_annotation = #loop_annotation}
  ^bb24:  // pred: ^bb7
    llvm.return
  }
  llvm.func linkonce_odr @_ZNSt6vectorIiSaIiEEixEm(%arg0: !llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, %arg1: i64 {llvm.noundef}) -> (!llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}) comdat(@__llvm_global_comdat::@_ZNSt6vectorIiSaIiEEixEm) attributes {alignment = 2 : i64, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_inline, no_unwind, optimize_none, passthrough = ["mustprogress", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.mlir.constant(0 : i32) : i32
    %2 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %3 = llvm.alloca %0 x i64 {alignment = 8 : i64} : (i32) -> !llvm.ptr
    llvm.store %arg0, %2 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    llvm.store %arg1, %3 {alignment = 8 : i64} : i64, !llvm.ptr
    %4 = llvm.load %2 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %5 = llvm.getelementptr inbounds %4[%1, 0] : (!llvm.ptr, i32) -> !llvm.ptr, !llvm.struct<"struct.std::_Vector_base", (struct<"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl", (struct<"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data", (ptr, ptr, ptr)>)>)>
    %6 = llvm.getelementptr inbounds %5[%1, 0] : (!llvm.ptr, i32) -> !llvm.ptr, !llvm.struct<"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data", (ptr, ptr, ptr)>
    %7 = llvm.load %6 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %8 = llvm.load %3 {alignment = 8 : i64} : !llvm.ptr -> i64
    %9 = llvm.getelementptr inbounds %7[%8] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.return %9 : !llvm.ptr
  }
  llvm.func linkonce_odr @_ZNKSt6vectorIiSaIiEEixEm(%arg0: !llvm.ptr {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, %arg1: i64 {llvm.noundef}) -> (!llvm.ptr {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}) comdat(@__llvm_global_comdat::@_ZNKSt6vectorIiSaIiEEixEm) attributes {alignment = 2 : i64, dso_local, frame_pointer = #llvm.framePointerKind<all>, no_inline, no_unwind, optimize_none, passthrough = ["mustprogress", ["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], target_cpu = "x86-64", target_features = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, tune_cpu = "generic", uwtable_kind = #llvm.uwtableKind<async>} {
    %0 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.mlir.constant(0 : i32) : i32
    %2 = llvm.alloca %0 x !llvm.ptr {alignment = 8 : i64} : (i32) -> !llvm.ptr
    %3 = llvm.alloca %0 x i64 {alignment = 8 : i64} : (i32) -> !llvm.ptr
    llvm.store %arg0, %2 {alignment = 8 : i64} : !llvm.ptr, !llvm.ptr
    llvm.store %arg1, %3 {alignment = 8 : i64} : i64, !llvm.ptr
    %4 = llvm.load %2 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %5 = llvm.getelementptr inbounds %4[%1, 0] : (!llvm.ptr, i32) -> !llvm.ptr, !llvm.struct<"struct.std::_Vector_base", (struct<"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl", (struct<"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data", (ptr, ptr, ptr)>)>)>
    %6 = llvm.getelementptr inbounds %5[%1, 0] : (!llvm.ptr, i32) -> !llvm.ptr, !llvm.struct<"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data", (ptr, ptr, ptr)>
    %7 = llvm.load %6 {alignment = 8 : i64} : !llvm.ptr -> !llvm.ptr
    %8 = llvm.load %3 {alignment = 8 : i64} : !llvm.ptr -> i64
    %9 = llvm.getelementptr inbounds %7[%8] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.return %9 : !llvm.ptr
  }
}
