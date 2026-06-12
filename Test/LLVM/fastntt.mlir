// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// This file contains a very naive implementation of the FastNTT algorithm, based on the heir pseudocode
// (https://github.com/google/heir/blob/1210ad37dc9531d6e60d8ddbce81dbd79f7626a6/lib/Dialect/Polynomial/Conversions/PolynomialToModArith/PolynomialToModArith.cpp#L1060) and lowered using the `Vcc` tool (see `Test/Vcc/fastntt.c`).

"builtin.module"() ({
  ^4():
    "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
    "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, dso_local, "frame_pointer" = #llvm.framePointerKind<all>, "function_type" = !llvm.func<i32 ()>, "linkage" = #llvm.linkage<external>, no_inline, no_unwind, "passthrough" = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], "sym_name" = "main", "target_cpu" = "x86-64", "target_features" = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, "tune_cpu" = "generic", "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<async>, "visibility_" = 0 : i64}> ({
      ^7():
        %8 = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
        %9 = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
        %10 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
        %11 = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
        %12 = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
        %13 = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
        %14 = "llvm.mlir.constant"() <{"value" = 8 : i64}> : () -> i64
        %15 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
        %16 = "llvm.mlir.constant"() <{"value" = 17 : i64}> : () -> i64
        %17 = "llvm.alloca"(%8) <{"alignment" = 16 : i64, "elem_type" = !llvm.array<4 x i64>}> : (i32) -> !llvm.ptr
        %18 = "llvm.alloca"(%8) <{"alignment" = 16 : i64, "elem_type" = !llvm.array<8 x i64>}> : (i32) -> !llvm.ptr
        %19 = "llvm.getelementptr"(%17, %9, %9) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%10, %19) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 16 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        %21 = "llvm.getelementptr"(%17, %9, %10) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%11, %21) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        %23 = "llvm.getelementptr"(%17, %9, %11) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%12, %23) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 16 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        %25 = "llvm.getelementptr"(%17, %9, %12) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%13, %25) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        "llvm.br"(%10, %9) [^28] : (i64, i64) -> ()
      ^28(%arg28_0 : i64, %arg28_1 : i64):
        %30 = "llvm.icmp"(%arg28_1, %14) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%30) [^31, ^32] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^31():
        %34 = "llvm.getelementptr"(%18, %9, %arg28_1) <{"elem_type" = !llvm.array<8 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%arg28_0, %34) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        %36 = "llvm.mul"(%arg28_0, %12) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %37 = "llvm.srem"(%36, %16) : (i64, i64) -> i64
        "llvm.br"() [^38] : () -> ()
      ^38():
        %40 = "llvm.add"(%arg28_1, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%37, %40) [^28] : (i64, i64) -> ()
      ^32():
        %42 = "llvm.getelementptr"(%17, %9, %9) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %43 = "llvm.getelementptr"(%18, %9, %9) <{"elem_type" = !llvm.array<8 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %44 = "llvm.icmp"(%9, %9) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%44) [^45, ^46] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^45():
        "llvm.br"(%13) [^48] : (i64) -> ()
      ^46():
        "llvm.br"(%11) [^48] : (i64) -> ()
      ^48(%arg48_0 : i64):
        %51 = "llvm.icmp"(%9, %9) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%51) [^52, ^53] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^52():
        "llvm.br"(%10) [^55] : (i64) -> ()
      ^53():
        %57 = "llvm.sdiv"(%13, %11) : (i64, i64) -> i64
        "llvm.br"(%57) [^55] : (i64) -> ()
      ^55(%arg55_0 : i64):
        %59 = "llvm.sdiv"(%13, %11) : (i64, i64) -> i64
        "llvm.br"(%9, %59, %arg55_0, %arg48_0) [^60] : (i64, i64, i64, i64) -> ()
      ^60(%arg60_0 : i64, %arg60_1 : i64, %arg60_2 : i64, %arg60_3 : i64):
        "llvm.br"(%9, %13) [^62] : (i64, i64) -> ()
      ^62(%arg62_0 : i64, %arg62_1 : i64):
        %64 = "llvm.icmp"(%arg62_1, %10) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%64) [^65, ^66] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^65():
        %68 = "llvm.ashr"(%arg62_1, %10) : (i64, i64) -> i64
        %69 = "llvm.add"(%arg62_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%69, %68) [^62] : (i64, i64) -> ()
      ^66():
        %71 = "llvm.icmp"(%arg60_0, %arg62_0) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%71) [^72, ^73] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^72():
        "llvm.br"(%9) [^75] : (i64) -> ()
      ^75(%arg75_0 : i64):
        %77 = "llvm.sdiv"(%13, %arg60_3) : (i64, i64) -> i64
        %78 = "llvm.icmp"(%arg75_0, %77) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%78) [^79, ^80] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^79():
        "llvm.br"(%9) [^82] : (i64) -> ()
      ^82(%arg82_0 : i64):
        %84 = "llvm.sdiv"(%arg60_3, %11) : (i64, i64) -> i64
        %85 = "llvm.icmp"(%arg82_0, %84) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%85) [^86, ^87] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^86():
        %89 = "llvm.mul"(%arg75_0, %arg60_3) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %90 = "llvm.add"(%89, %arg82_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %91 = "llvm.getelementptr"(%42, %90) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %92 = "llvm.load"(%91) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
        %95 = "llvm.sdiv"(%arg60_3, %11) : (i64, i64) -> i64
        %96 = "llvm.add"(%90, %95) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %97 = "llvm.getelementptr"(%42, %96) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %98 = "llvm.load"(%97) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
        %99 = "llvm.mul"(%11, %arg82_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %100 = "llvm.add"(%99, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %101 = "llvm.mul"(%100, %arg60_1) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %102 = "llvm.getelementptr"(%43, %101) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %103 = "llvm.load"(%102) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
        %104 = "llvm.mul"(%103, %98) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %105 = "llvm.srem"(%104, %16) : (i64, i64) -> i64
        %106 = "llvm.add"(%92, %105) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %107 = "llvm.srem"(%106, %16) : (i64, i64) -> i64
        %110 = "llvm.sub"(%92, %105) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %111 = "llvm.add"(%110, %16) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %112 = "llvm.srem"(%111, %16) : (i64, i64) -> i64
        %115 = "llvm.getelementptr"(%42, %90) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%107, %115) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        %121 = "llvm.getelementptr"(%42, %96) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%112, %121) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        %123 = "llvm.add"(%arg82_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%123) [^82] : (i64) -> ()
      ^87():
        %125 = "llvm.add"(%arg75_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%125) [^75] : (i64) -> ()
      ^80():
        %127 = "llvm.sdiv"(%arg60_1, %11) : (i64, i64) -> i64
        %128 = "llvm.icmp"(%9, %9) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%128) [^129, ^130] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^129():
        %132 = "llvm.sdiv"(%arg60_3, %11) : (i64, i64) -> i64
        "llvm.br"(%132) [^133] : (i64) -> ()
      ^130():
        %152 = "llvm.add"(%arg60_3, %arg60_3) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%152) [^133] : (i64) -> ()
      ^133(%arg133_0 : i64):
        %137 = "llvm.icmp"(%9, %9) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%137) [^138, ^139] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^138():
        %151 = "llvm.add"(%arg60_2, %arg60_2) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%151) [^142] : (i64) -> ()
      ^139():
        %144 = "llvm.sdiv"(%arg60_2, %11) : (i64, i64) -> i64
        "llvm.br"(%144) [^142] : (i64) -> ()
      ^142(%arg142_0 : i64):
        %146 = "llvm.add"(%arg60_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%146, %127, %arg142_0, %arg133_0) [^60] : (i64, i64, i64, i64) -> ()
      ^73():
        "llvm.return"(%15) : (i32) -> ()
    }) : () -> ()
}) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, "llvm.ident" = "Ubuntu clang version 18.1.3 (1ubuntu1)", "llvm.module_asm" = [], "llvm.target_triple" = "x86_64-pc-linux-gnu"} : () -> ()



// CHECK:      "builtin.module"() ({
// CHECK-NEXT: ^[[BB4:[0-9]+]]():
// CHECK-NEXT:   "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
// CHECK-NEXT:   "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, dso_local, "frame_pointer" = #llvm.framePointerKind<all>, "function_type" = !llvm.func<i32 ()>, "linkage" = #llvm.linkage<external>, no_inline, no_unwind, "passthrough" = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "{{.*}}"]], "sym_name" = "main", "target_cpu" = "{{.*}}", "target_features" = #llvm.target_features<[{{.*}}]>, "tune_cpu" = "{{.*}}", "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<async>, "visibility_" = 0 : i64}> ({
// CHECK-NEXT:   ^[[BB7:[0-9]+]]():
// CHECK-NEXT:     %[[M_C1:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:     %[[M_C0:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C1_64:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C2:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C3:.*]] = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C4:.*]] = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C8:.*]] = "llvm.mlir.constant"() <{"value" = 8 : i64}> : () -> i64
// CHECK-NEXT:     %[[M_C0_32:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:     %[[M_C17:.*]] = "llvm.mlir.constant"() <{"value" = 17 : i64}> : () -> i64
// CHECK-NEXT:     %[[ALLOC17:.*]] = "llvm.alloca"(%[[M_C1]]) <{"alignment" = 16 : i64, "elem_type" = !llvm.array<4 x i64>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:     %[[ALLOC18:.*]] = "llvm.alloca"(%[[M_C1]]) <{"alignment" = 16 : i64, "elem_type" = !llvm.array<8 x i64>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:     %[[GEP19:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C0]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[M_C1_64]], %[[GEP19]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 16 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[GEP21:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C1_64]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[M_C2]], %[[GEP21]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[GEP23:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C2]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[M_C3]], %[[GEP23]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 16 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[GEP25:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C3]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[M_C4]], %[[GEP25]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     "llvm.br"(%[[M_C1_64]], %[[M_C0]]) [^[[BB28:[0-9]+]]] : (i64, i64) -> ()
// CHECK-NEXT:   ^[[BB28]](%[[ARG28_0:.*]] : i64, %[[ARG28_1:.*]] : i64):
// CHECK-NEXT:     %[[CMP30:.*]] = "llvm.icmp"(%[[ARG28_1]], %[[M_C8]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP30]]) [^[[BB31:[0-9]+]], ^[[BB32:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB31]]():
// CHECK-NEXT:     %[[GEP34:.*]] = "llvm.getelementptr"(%[[ALLOC18]], %[[M_C0]], %[[ARG28_1]]) <{"elem_type" = !llvm.array<8 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[ARG28_0]], %[[GEP34]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[MUL36:.*]] = "llvm.mul"(%[[ARG28_0]], %[[M_C3]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[SREM37:.*]] = "llvm.srem"(%[[MUL36]], %[[M_C17]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"() [^[[BB38:[0-9]+]]] : () -> ()
// CHECK-NEXT:   ^[[BB38]]():
// CHECK-NEXT:     %[[ADD40:.*]] = "llvm.add"(%[[ARG28_1]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[SREM37]], %[[ADD40]]) [^[[BB28]]] : (i64, i64) -> ()
// CHECK-NEXT:   ^[[BB32]]():
// CHECK-NEXT:     %[[GEP42:.*]] = "llvm.getelementptr"(%[[ALLOC17]], %[[M_C0]], %[[M_C0]]) <{"elem_type" = !llvm.array<4 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[GEP43:.*]] = "llvm.getelementptr"(%[[ALLOC18]], %[[M_C0]], %[[M_C0]]) <{"elem_type" = !llvm.array<8 x i64>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[CMP44:.*]] = "llvm.icmp"(%[[M_C0]], %[[M_C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP44]]) [^[[BB45:[0-9]+]], ^[[BB46:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB45]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C4]]) [^[[BB48:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB46]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C2]]) [^[[BB48]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB48]](%[[ARG48_0:.*]] : i64):
// CHECK-NEXT:     %[[CMP51:.*]] = "llvm.icmp"(%[[M_C0]], %[[M_C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP51]]) [^[[BB52:[0-9]+]], ^[[BB53:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB52]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C1_64]]) [^[[BB55:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB53]]():
// CHECK-NEXT:     %[[DIV57:.*]] = "llvm.sdiv"(%[[M_C4]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[DIV57]]) [^[[BB55]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB55]](%[[ARG55_0:.*]] : i64):
// CHECK-NEXT:     %[[DIV59:.*]] = "llvm.sdiv"(%[[M_C4]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[M_C0]], %[[DIV59]], %[[ARG55_0]], %[[ARG48_0]]) [^[[BB60:[0-9]+]]] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT:   ^[[BB60]](%[[ARG60_0:.*]] : i64, %[[ARG60_1:.*]] : i64, %[[ARG60_2:.*]] : i64, %[[ARG60_3:.*]] : i64):
// CHECK-NEXT:     "llvm.br"(%[[M_C0]], %[[M_C4]]) [^[[BB62:[0-9]+]]] : (i64, i64) -> ()
// CHECK-NEXT:   ^[[BB62]](%[[ARG62_0:.*]] : i64, %[[ARG62_1:.*]] : i64):
// CHECK-NEXT:     %[[CMP64:.*]] = "llvm.icmp"(%[[ARG62_1]], %[[M_C1_64]]) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP64]]) [^[[BB65:[0-9]+]], ^[[BB66:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB65]]():
// CHECK-NEXT:     %[[ASHR68:.*]] = "llvm.ashr"(%[[ARG62_1]], %[[M_C1_64]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD69:.*]] = "llvm.add"(%[[ARG62_0]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD69]], %[[ASHR68]]) [^[[BB62]]] : (i64, i64) -> ()
// CHECK-NEXT:   ^[[BB66]]():
// CHECK-NEXT:     %[[CMP71:.*]] = "llvm.icmp"(%[[ARG60_0]], %[[ARG62_0]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP71]]) [^[[BB72:[0-9]+]], ^[[BB73:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB72]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C0]]) [^[[BB75:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB75]](%[[ARG75_0:.*]] : i64):
// CHECK-NEXT:     %[[DIV77:.*]] = "llvm.sdiv"(%[[M_C4]], %[[ARG60_3]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[CMP78:.*]] = "llvm.icmp"(%[[ARG75_0]], %[[DIV77]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP78]]) [^[[BB79:[0-9]+]], ^[[BB80:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB79]]():
// CHECK-NEXT:     "llvm.br"(%[[M_C0]]) [^[[BB82:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB82]](%[[ARG82_0:.*]] : i64):
// CHECK-NEXT:     %[[DIV84:.*]] = "llvm.sdiv"(%[[ARG60_3]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[CMP85:.*]] = "llvm.icmp"(%[[ARG82_0]], %[[DIV84]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP85]]) [^[[BB86:[0-9]+]], ^[[BB87:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB86]]():
// CHECK-NEXT:     %[[MUL89:.*]] = "llvm.mul"(%[[ARG75_0]], %[[ARG60_3]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD90:.*]] = "llvm.add"(%[[MUL89]], %[[ARG82_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[GEP91:.*]] = "llvm.getelementptr"(%[[GEP42]], %[[ADD90]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[LOAD92:.*]] = "llvm.load"(%[[GEP91]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:     %[[DIV95:.*]] = "llvm.sdiv"(%[[ARG60_3]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD96:.*]] = "llvm.add"(%[[ADD90]], %[[DIV95]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[GEP97:.*]] = "llvm.getelementptr"(%[[GEP42]], %[[ADD96]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[LOAD98:.*]] = "llvm.load"(%[[GEP97]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:     %[[MUL99:.*]] = "llvm.mul"(%[[M_C2]], %[[ARG82_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD100:.*]] = "llvm.add"(%[[MUL99]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[MUL101:.*]] = "llvm.mul"(%[[ADD100]], %[[ARG60_1]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[GEP102:.*]] = "llvm.getelementptr"(%[[GEP43]], %[[MUL101]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     %[[LOAD103:.*]] = "llvm.load"(%[[GEP102]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:     %[[MUL104:.*]] = "llvm.mul"(%[[LOAD103]], %[[LOAD98]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[SREM105:.*]] = "llvm.srem"(%[[MUL104]], %[[M_C17]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD106:.*]] = "llvm.add"(%[[LOAD92]], %[[SREM105]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[SREM107:.*]] = "llvm.srem"(%[[ADD106]], %[[M_C17]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[SUB110:.*]] = "llvm.sub"(%[[LOAD92]], %[[SREM105]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[ADD111:.*]] = "llvm.add"(%[[SUB110]], %[[M_C17]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     %[[SREM112:.*]] = "llvm.srem"(%[[ADD111]], %[[M_C17]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[GEP115:.*]] = "llvm.getelementptr"(%[[GEP42]], %[[ADD90]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[SREM107]], %[[GEP115]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[GEP121:.*]] = "llvm.getelementptr"(%[[GEP42]], %[[ADD96]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:     "llvm.store"(%[[SREM112]], %[[GEP121]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:     %[[ADD123:.*]] = "llvm.add"(%[[ARG82_0]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD123]]) [^[[BB82]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB87]]():
// CHECK-NEXT:     %[[ADD125:.*]] = "llvm.add"(%[[ARG75_0]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD125]]) [^[[BB75]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB80]]():
// CHECK-NEXT:     %[[DIV127:.*]] = "llvm.sdiv"(%[[ARG60_1]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     %[[CMP128:.*]] = "llvm.icmp"(%[[M_C0]], %[[M_C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP128]]) [^[[BB129:[0-9]+]], ^[[BB130:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB129]]():
// CHECK-NEXT:     %[[DIV132:.*]] = "llvm.sdiv"(%[[ARG60_3]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[DIV132]]) [^[[BB133:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB130]]():
// CHECK-NEXT:     %[[ADD152:.*]] = "llvm.add"(%[[ARG60_3]], %[[ARG60_3]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD152]]) [^[[BB133]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB133]](%[[ARG133_0:.*]] : i64):
// CHECK-NEXT:     %[[CMP137:.*]] = "llvm.icmp"(%[[M_C0]], %[[M_C0]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     "llvm.cond_br"(%[[CMP137]]) [^[[BB138:[0-9]+]], ^[[BB139:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:   ^[[BB138]]():
// CHECK-NEXT:     %[[ADD151:.*]] = "llvm.add"(%[[ARG60_2]], %[[ARG60_2]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD151]]) [^[[BB142:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB139]]():
// CHECK-NEXT:     %[[DIV144:.*]] = "llvm.sdiv"(%[[ARG60_2]], %[[M_C2]]) : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[DIV144]]) [^[[BB142]]] : (i64) -> ()
// CHECK-NEXT:   ^[[BB142]](%[[ARG142_0:.*]] : i64):
// CHECK-NEXT:     %[[ADD146:.*]] = "llvm.add"(%[[ARG60_0]], %[[M_C1_64]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:     "llvm.br"(%[[ADD146]], %[[DIV127]], %[[ARG142_0]], %[[ARG133_0]]) [^[[BB60]]] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT:   ^[[BB73]]():
// CHECK-NEXT:     "llvm.return"(%[[M_C0_32]]) : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()
