// RUN: veir-opt %s -p=isel-br-riscv64,isel-riscv64,reconcile-cast | filecheck %s

"builtin.module"() ({
  ^4():
    "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 1 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 4 : i32>]}> : () -> ()
    "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, always_inline, "frame_pointer" = #llvm.framePointerKind<"non-leaf-no-reserve">, "function_type" = !llvm.func<i32 ()>, "linkage" = #llvm.linkage<external>, no_unwind, "passthrough" = ["ssp", ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "apple-m1"]], "sym_name" = "chacha20", "target_cpu" = "apple-m1", "target_features" = #llvm.target_features<["+aes", "+altnzcv", "+ccdp", "+ccidx", "+ccpp", "+complxnum", "+crc", "+dit", "+dotprod", "+flagm", "+fp-armv8", "+fp16fml", "+fptoint", "+fullfp16", "+jsconv", "+lse", "+neon", "+pauth", "+perfmon", "+predres", "+ras", "+rcpc", "+rdm", "+sb", "+sha2", "+sha3", "+specrestrict", "+ssbs", "+v8.1a", "+v8.2a", "+v8.3a", "+v8.4a", "+v8a"]>, "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<sync>, "visibility_" = 0 : i64}> ({
      ^7():
        %8 = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
        %9 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
        %10 = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
        %11 = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
        %12 = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
        %13 = "llvm.mlir.constant"() <{"value" = 7 : i64}> : () -> i64
        %14 = "llvm.mlir.constant"() <{"value" = 74 : i8}> : () -> i8
        %15 = "llvm.mlir.constant"() <{"value" = 114 : i32}> : () -> i32
        %16 = "llvm.mlir.constant"() <{"value" = 76 : i8}> : () -> i8
        %17 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
        %18 = "llvm.mlir.constant"() <{"value" = 97 : i8}> : () -> i8
        %19 = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
        %20 = "llvm.mlir.constant"() <{"value" = 100 : i8}> : () -> i8
        %21 = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
        %22 = "llvm.mlir.constant"() <{"value" = 105 : i8}> : () -> i8
        %23 = "llvm.mlir.constant"() <{"value" = 114 : i64}> : () -> i64
        %24 = "llvm.mlir.constant"() <{"value" = 24 : i32}> : () -> i32
        %25 = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
        %26 = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
        %27 = "llvm.mlir.constant"() <{"value" = 1634760805 : i32}> : () -> i32
        %28 = "llvm.mlir.constant"() <{"value" = 857760878 : i32}> : () -> i32
        %29 = "llvm.mlir.constant"() <{"value" = 2036477234 : i32}> : () -> i32
        %30 = "llvm.mlir.constant"() <{"value" = 1797285236 : i32}> : () -> i32
        %31 = "llvm.mlir.constant"() <{"value" = 12 : i64}> : () -> i64
        %32 = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
        %33 = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
        %34 = "llvm.mlir.constant"() <{"value" = 64 : i64}> : () -> i64
        %35 = "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
        %36 = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
        %37 = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
        %38 = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
        %39 = "llvm.mlir.constant"() <{"value" = 9 : i32}> : () -> i32
        %40 = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
        %41 = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
        %42 = "llvm.mlir.constant"() <{"value" = 14 : i32}> : () -> i32
        %43 = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
        %44 = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
        %45 = "llvm.mlir.constant"() <{"value" = 0 : i8}> : () -> i8
        %46 = "llvm.alloca"(%8) <{"alignment" = 4 : i64, "elem_type" = !llvm.array<16 x i32>}> : (i32) -> !llvm.ptr
        %47 = "llvm.alloca"(%8) <{"alignment" = 4 : i64, "elem_type" = !llvm.array<16 x i32>}> : (i32) -> !llvm.ptr
        %48 = "llvm.alloca"(%8) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<64 x i8>}> : (i32) -> !llvm.ptr
        %49 = "llvm.alloca"(%8) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
        %50 = "llvm.alloca"(%8) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<12 x i8>}> : (i32) -> !llvm.ptr
        %51 = "llvm.alloca"(%8) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<114 x i8>}> : (i32) -> !llvm.ptr
        %52 = "llvm.alloca"(%8) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<114 x i8>}> : (i32) -> !llvm.ptr
        "llvm.br"(%9) [^53] : (i32) -> ()
      ^53(%arg53_0 : i32):
        %55 = "llvm.icmp"(%arg53_0, %10) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%55) [^56, ^57] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^56():
        %59 = "llvm.trunc"(%arg53_0) : (i32) -> i8
        %60 = "llvm.sext"(%arg53_0) : (i32) -> i64
        %61 = "llvm.getelementptr"(%49, %12, %60) <{"elem_type" = !llvm.array<32 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%59, %61) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        "llvm.br"() [^63] : () -> ()
      ^63():
        %65 = "llvm.add"(%arg53_0, %8) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%65) [^53] : (i32) -> ()
      ^57():
        "llvm.br"(%9) [^67] : (i32) -> ()
      ^67(%arg67_0 : i32):
        %69 = "llvm.icmp"(%arg67_0, %11) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%69) [^70, ^71] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^70():
        %73 = "llvm.sext"(%arg67_0) : (i32) -> i64
        %74 = "llvm.getelementptr"(%50, %12, %73) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%45, %74) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        "llvm.br"() [^76] : () -> ()
      ^76():
        %78 = "llvm.add"(%arg67_0, %8) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%78) [^67] : (i32) -> ()
      ^71():
        %80 = "llvm.getelementptr"(%50, %12, %13) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%14, %80) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        "llvm.br"(%9) [^82] : (i32) -> ()
      ^82(%arg82_0 : i32):
        %84 = "llvm.icmp"(%arg82_0, %15) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%84) [^85, ^86] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^85():
        %88 = "llvm.sext"(%arg82_0) : (i32) -> i64
        %89 = "llvm.getelementptr"(%51, %12, %88) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%45, %89) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        "llvm.br"() [^91] : () -> ()
      ^91():
        %93 = "llvm.add"(%arg82_0, %8) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%93) [^82] : (i32) -> ()
      ^86():
        %95 = "llvm.getelementptr"(%51, %12, %12) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%16, %95) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %97 = "llvm.getelementptr"(%51, %12, %17) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%18, %97) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %99 = "llvm.getelementptr"(%51, %12, %19) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%20, %99) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %101 = "llvm.getelementptr"(%51, %12, %21) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%22, %101) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %103 = "llvm.getelementptr"(%49, %12, %12) <{"elem_type" = !llvm.array<32 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %104 = "llvm.getelementptr"(%50, %12, %12) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %105 = "llvm.getelementptr"(%51, %12, %12) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %106 = "llvm.getelementptr"(%52, %12, %12) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.br"(%8, %12) [^107] : (i32, i64) -> ()
      ^107(%arg107_0 : i32, %arg107_1 : i64):
        %109 = "llvm.icmp"(%arg107_1, %23) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%109) [^110, ^111] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^110():
        "llvm.store"(%27, %46) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %114 = "llvm.getelementptr"(%46, %12, %17) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%28, %114) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %116 = "llvm.getelementptr"(%46, %12, %19) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%29, %116) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %118 = "llvm.getelementptr"(%46, %12, %21) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%30, %118) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"(%9) [^120] : (i32) -> ()
      ^120(%arg120_0 : i32):
        %122 = "llvm.icmp"(%arg120_0, %26) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%122) [^123, ^124] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^123():
        %126 = "llvm.mul"(%35, %arg120_0) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %127 = "llvm.sext"(%126) : (i32) -> i64
        %128 = "llvm.getelementptr"(%103, %127) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %129 = "llvm.load"(%128) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %130 = "llvm.zext"(%129) : (i8) -> i32
        %131 = "llvm.getelementptr"(%128, %17) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %132 = "llvm.load"(%131) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %133 = "llvm.zext"(%132) : (i8) -> i32
        %134 = "llvm.shl"(%133, %26) : (i32, i32) -> i32
        %135 = "llvm.or"(%130, %134) : (i32, i32) -> i32
        %136 = "llvm.getelementptr"(%128, %19) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %137 = "llvm.load"(%136) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %138 = "llvm.zext"(%137) : (i8) -> i32
        %139 = "llvm.shl"(%138, %25) : (i32, i32) -> i32
        %140 = "llvm.or"(%135, %139) : (i32, i32) -> i32
        %141 = "llvm.getelementptr"(%128, %21) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %142 = "llvm.load"(%141) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %143 = "llvm.zext"(%142) : (i8) -> i32
        %144 = "llvm.shl"(%143, %24) : (i32, i32) -> i32
        %145 = "llvm.or"(%140, %144) : (i32, i32) -> i32
        %146 = "llvm.add"(%35, %arg120_0) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %147 = "llvm.sext"(%146) : (i32) -> i64
        %148 = "llvm.getelementptr"(%46, %12, %147) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%145, %148) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %150 = "llvm.add"(%arg120_0, %8) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%150) [^120] : (i32) -> ()
      ^124():
        %152 = "llvm.getelementptr"(%46, %12, %31) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%arg107_0, %152) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"(%9) [^154] : (i32) -> ()
      ^154(%arg154_0 : i32):
        %156 = "llvm.icmp"(%arg154_0, %32) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%156) [^157, ^158] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^157():
        %160 = "llvm.mul"(%35, %arg154_0) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %161 = "llvm.sext"(%160) : (i32) -> i64
        %162 = "llvm.getelementptr"(%104, %161) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %163 = "llvm.load"(%162) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %164 = "llvm.zext"(%163) : (i8) -> i32
        %165 = "llvm.getelementptr"(%162, %17) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %166 = "llvm.load"(%165) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %167 = "llvm.zext"(%166) : (i8) -> i32
        %168 = "llvm.shl"(%167, %26) : (i32, i32) -> i32
        %169 = "llvm.or"(%164, %168) : (i32, i32) -> i32
        %170 = "llvm.getelementptr"(%162, %19) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %171 = "llvm.load"(%170) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %172 = "llvm.zext"(%171) : (i8) -> i32
        %173 = "llvm.shl"(%172, %25) : (i32, i32) -> i32
        %174 = "llvm.or"(%169, %173) : (i32, i32) -> i32
        %175 = "llvm.getelementptr"(%162, %21) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %176 = "llvm.load"(%175) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %177 = "llvm.zext"(%176) : (i8) -> i32
        %178 = "llvm.shl"(%177, %24) : (i32, i32) -> i32
        %179 = "llvm.or"(%174, %178) : (i32, i32) -> i32
        %180 = "llvm.add"(%38, %arg154_0) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %181 = "llvm.sext"(%180) : (i32) -> i64
        %182 = "llvm.getelementptr"(%46, %12, %181) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%179, %182) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %184 = "llvm.add"(%arg154_0, %8) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%184) [^154] : (i32) -> ()
      ^158():
        "llvm.br"(%9) [^186] : (i32) -> ()
      ^186(%arg186_0 : i32):
        %188 = "llvm.icmp"(%arg186_0, %25) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%188) [^189, ^190] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^189():
        %192 = "llvm.sext"(%arg186_0) : (i32) -> i64
        %193 = "llvm.getelementptr"(%46, %12, %192) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %194 = "llvm.load"(%193) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %196 = "llvm.getelementptr"(%47, %12, %192) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        "llvm.store"(%194, %196) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %198 = "llvm.add"(%arg186_0, %8) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%198) [^186] : (i32) -> ()
      ^190():
        "llvm.br"(%9) [^200] : (i32) -> ()
      ^200(%arg200_0 : i32):
        %202 = "llvm.icmp"(%arg200_0, %33) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%202) [^203, ^204] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^203():
        %206 = "llvm.sext"(%35) : (i32) -> i64
        %207 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %208 = "llvm.load"(%207) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %209 = "llvm.sext"(%9) : (i32) -> i64
        %210 = "llvm.getelementptr"(%47, %209) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %211 = "llvm.load"(%210) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %212 = "llvm.add"(%211, %208) : (i32, i32) -> i32
        "llvm.store"(%212, %210) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %215 = "llvm.getelementptr"(%47, %209) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %216 = "llvm.load"(%215) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %217 = "llvm.sext"(%11) : (i32) -> i64
        %218 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %219 = "llvm.load"(%218) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %220 = "llvm.xor"(%219, %216) : (i32, i32) -> i32
        "llvm.store"(%220, %218) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %223 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %224 = "llvm.load"(%223) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %225 = "llvm.shl"(%224, %25) : (i32, i32) -> i32
        %226 = "llvm.sub"(%10, %25) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %227 = "llvm.lshr"(%224, %226) : (i32, i32) -> i32
        %228 = "llvm.or"(%225, %227) : (i32, i32) -> i32
        %230 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%228, %230) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %233 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %234 = "llvm.load"(%233) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %235 = "llvm.sext"(%26) : (i32) -> i64
        %236 = "llvm.getelementptr"(%47, %235) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %237 = "llvm.load"(%236) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %238 = "llvm.add"(%237, %234) : (i32, i32) -> i32
        "llvm.store"(%238, %236) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %241 = "llvm.getelementptr"(%47, %235) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %242 = "llvm.load"(%241) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %244 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %245 = "llvm.load"(%244) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %246 = "llvm.xor"(%245, %242) : (i32, i32) -> i32
        "llvm.store"(%246, %244) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %249 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %250 = "llvm.load"(%249) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %251 = "llvm.shl"(%250, %11) : (i32, i32) -> i32
        %252 = "llvm.sub"(%10, %11) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %253 = "llvm.lshr"(%250, %252) : (i32, i32) -> i32
        %254 = "llvm.or"(%251, %253) : (i32, i32) -> i32
        %256 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%254, %256) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %259 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %260 = "llvm.load"(%259) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %262 = "llvm.getelementptr"(%47, %209) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %263 = "llvm.load"(%262) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %264 = "llvm.add"(%263, %260) : (i32, i32) -> i32
        "llvm.store"(%264, %262) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %267 = "llvm.getelementptr"(%47, %209) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %268 = "llvm.load"(%267) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %270 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %271 = "llvm.load"(%270) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %272 = "llvm.xor"(%271, %268) : (i32, i32) -> i32
        "llvm.store"(%272, %270) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %275 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %276 = "llvm.load"(%275) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %277 = "llvm.shl"(%276, %26) : (i32, i32) -> i32
        %278 = "llvm.sub"(%10, %26) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %279 = "llvm.lshr"(%276, %278) : (i32, i32) -> i32
        %280 = "llvm.or"(%277, %279) : (i32, i32) -> i32
        %282 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%280, %282) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %285 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %286 = "llvm.load"(%285) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %288 = "llvm.getelementptr"(%47, %235) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %289 = "llvm.load"(%288) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %290 = "llvm.add"(%289, %286) : (i32, i32) -> i32
        "llvm.store"(%290, %288) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %293 = "llvm.getelementptr"(%47, %235) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %294 = "llvm.load"(%293) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %296 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %297 = "llvm.load"(%296) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %298 = "llvm.xor"(%297, %294) : (i32, i32) -> i32
        "llvm.store"(%298, %296) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %301 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %302 = "llvm.load"(%301) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %303 = "llvm.shl"(%302, %36) : (i32, i32) -> i32
        %304 = "llvm.sub"(%10, %36) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %305 = "llvm.lshr"(%302, %304) : (i32, i32) -> i32
        %306 = "llvm.or"(%303, %305) : (i32, i32) -> i32
        %308 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%306, %308) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %310 = "llvm.sext"(%37) : (i32) -> i64
        %311 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %312 = "llvm.load"(%311) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %313 = "llvm.sext"(%8) : (i32) -> i64
        %314 = "llvm.getelementptr"(%47, %313) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %315 = "llvm.load"(%314) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %316 = "llvm.add"(%315, %312) : (i32, i32) -> i32
        "llvm.store"(%316, %314) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %319 = "llvm.getelementptr"(%47, %313) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %320 = "llvm.load"(%319) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %321 = "llvm.sext"(%38) : (i32) -> i64
        %322 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %323 = "llvm.load"(%322) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %324 = "llvm.xor"(%323, %320) : (i32, i32) -> i32
        "llvm.store"(%324, %322) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %327 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %328 = "llvm.load"(%327) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %329 = "llvm.shl"(%328, %25) : (i32, i32) -> i32
        %331 = "llvm.lshr"(%328, %226) : (i32, i32) -> i32
        %332 = "llvm.or"(%329, %331) : (i32, i32) -> i32
        %334 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%332, %334) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %337 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %338 = "llvm.load"(%337) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %339 = "llvm.sext"(%39) : (i32) -> i64
        %340 = "llvm.getelementptr"(%47, %339) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %341 = "llvm.load"(%340) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %342 = "llvm.add"(%341, %338) : (i32, i32) -> i32
        "llvm.store"(%342, %340) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %345 = "llvm.getelementptr"(%47, %339) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %346 = "llvm.load"(%345) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %348 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %349 = "llvm.load"(%348) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %350 = "llvm.xor"(%349, %346) : (i32, i32) -> i32
        "llvm.store"(%350, %348) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %353 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %354 = "llvm.load"(%353) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %355 = "llvm.shl"(%354, %11) : (i32, i32) -> i32
        %357 = "llvm.lshr"(%354, %252) : (i32, i32) -> i32
        %358 = "llvm.or"(%355, %357) : (i32, i32) -> i32
        %360 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%358, %360) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %363 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %364 = "llvm.load"(%363) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %366 = "llvm.getelementptr"(%47, %313) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %367 = "llvm.load"(%366) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %368 = "llvm.add"(%367, %364) : (i32, i32) -> i32
        "llvm.store"(%368, %366) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %371 = "llvm.getelementptr"(%47, %313) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %372 = "llvm.load"(%371) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %374 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %375 = "llvm.load"(%374) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %376 = "llvm.xor"(%375, %372) : (i32, i32) -> i32
        "llvm.store"(%376, %374) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %379 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %380 = "llvm.load"(%379) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %381 = "llvm.shl"(%380, %26) : (i32, i32) -> i32
        %383 = "llvm.lshr"(%380, %278) : (i32, i32) -> i32
        %384 = "llvm.or"(%381, %383) : (i32, i32) -> i32
        %386 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%384, %386) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %389 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %390 = "llvm.load"(%389) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %392 = "llvm.getelementptr"(%47, %339) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %393 = "llvm.load"(%392) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %394 = "llvm.add"(%393, %390) : (i32, i32) -> i32
        "llvm.store"(%394, %392) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %397 = "llvm.getelementptr"(%47, %339) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %398 = "llvm.load"(%397) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %400 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %401 = "llvm.load"(%400) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %402 = "llvm.xor"(%401, %398) : (i32, i32) -> i32
        "llvm.store"(%402, %400) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %405 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %406 = "llvm.load"(%405) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %407 = "llvm.shl"(%406, %36) : (i32, i32) -> i32
        %409 = "llvm.lshr"(%406, %304) : (i32, i32) -> i32
        %410 = "llvm.or"(%407, %409) : (i32, i32) -> i32
        %412 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%410, %412) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %414 = "llvm.sext"(%40) : (i32) -> i64
        %415 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %416 = "llvm.load"(%415) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %417 = "llvm.sext"(%41) : (i32) -> i64
        %418 = "llvm.getelementptr"(%47, %417) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %419 = "llvm.load"(%418) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %420 = "llvm.add"(%419, %416) : (i32, i32) -> i32
        "llvm.store"(%420, %418) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %423 = "llvm.getelementptr"(%47, %417) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %424 = "llvm.load"(%423) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %425 = "llvm.sext"(%42) : (i32) -> i64
        %426 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %427 = "llvm.load"(%426) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %428 = "llvm.xor"(%427, %424) : (i32, i32) -> i32
        "llvm.store"(%428, %426) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %431 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %432 = "llvm.load"(%431) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %433 = "llvm.shl"(%432, %25) : (i32, i32) -> i32
        %435 = "llvm.lshr"(%432, %226) : (i32, i32) -> i32
        %436 = "llvm.or"(%433, %435) : (i32, i32) -> i32
        %438 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%436, %438) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %441 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %442 = "llvm.load"(%441) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %443 = "llvm.sext"(%33) : (i32) -> i64
        %444 = "llvm.getelementptr"(%47, %443) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %445 = "llvm.load"(%444) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %446 = "llvm.add"(%445, %442) : (i32, i32) -> i32
        "llvm.store"(%446, %444) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %449 = "llvm.getelementptr"(%47, %443) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %450 = "llvm.load"(%449) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %452 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %453 = "llvm.load"(%452) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %454 = "llvm.xor"(%453, %450) : (i32, i32) -> i32
        "llvm.store"(%454, %452) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %457 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %458 = "llvm.load"(%457) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %459 = "llvm.shl"(%458, %11) : (i32, i32) -> i32
        %461 = "llvm.lshr"(%458, %252) : (i32, i32) -> i32
        %462 = "llvm.or"(%459, %461) : (i32, i32) -> i32
        %464 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%462, %464) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %467 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %468 = "llvm.load"(%467) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %470 = "llvm.getelementptr"(%47, %417) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %471 = "llvm.load"(%470) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %472 = "llvm.add"(%471, %468) : (i32, i32) -> i32
        "llvm.store"(%472, %470) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %475 = "llvm.getelementptr"(%47, %417) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %476 = "llvm.load"(%475) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %478 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %479 = "llvm.load"(%478) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %480 = "llvm.xor"(%479, %476) : (i32, i32) -> i32
        "llvm.store"(%480, %478) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %483 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %484 = "llvm.load"(%483) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %485 = "llvm.shl"(%484, %26) : (i32, i32) -> i32
        %487 = "llvm.lshr"(%484, %278) : (i32, i32) -> i32
        %488 = "llvm.or"(%485, %487) : (i32, i32) -> i32
        %490 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%488, %490) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %493 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %494 = "llvm.load"(%493) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %496 = "llvm.getelementptr"(%47, %443) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %497 = "llvm.load"(%496) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %498 = "llvm.add"(%497, %494) : (i32, i32) -> i32
        "llvm.store"(%498, %496) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %501 = "llvm.getelementptr"(%47, %443) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %502 = "llvm.load"(%501) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %504 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %505 = "llvm.load"(%504) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %506 = "llvm.xor"(%505, %502) : (i32, i32) -> i32
        "llvm.store"(%506, %504) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %509 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %510 = "llvm.load"(%509) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %511 = "llvm.shl"(%510, %36) : (i32, i32) -> i32
        %513 = "llvm.lshr"(%510, %304) : (i32, i32) -> i32
        %514 = "llvm.or"(%511, %513) : (i32, i32) -> i32
        %516 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%514, %516) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %518 = "llvm.sext"(%36) : (i32) -> i64
        %519 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %520 = "llvm.load"(%519) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %521 = "llvm.sext"(%32) : (i32) -> i64
        %522 = "llvm.getelementptr"(%47, %521) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %523 = "llvm.load"(%522) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %524 = "llvm.add"(%523, %520) : (i32, i32) -> i32
        "llvm.store"(%524, %522) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %527 = "llvm.getelementptr"(%47, %521) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %528 = "llvm.load"(%527) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %529 = "llvm.sext"(%43) : (i32) -> i64
        %530 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %531 = "llvm.load"(%530) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %532 = "llvm.xor"(%531, %528) : (i32, i32) -> i32
        "llvm.store"(%532, %530) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %535 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %536 = "llvm.load"(%535) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %537 = "llvm.shl"(%536, %25) : (i32, i32) -> i32
        %539 = "llvm.lshr"(%536, %226) : (i32, i32) -> i32
        %540 = "llvm.or"(%537, %539) : (i32, i32) -> i32
        %542 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%540, %542) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %545 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %546 = "llvm.load"(%545) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %547 = "llvm.sext"(%44) : (i32) -> i64
        %548 = "llvm.getelementptr"(%47, %547) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %549 = "llvm.load"(%548) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %550 = "llvm.add"(%549, %546) : (i32, i32) -> i32
        "llvm.store"(%550, %548) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %553 = "llvm.getelementptr"(%47, %547) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %554 = "llvm.load"(%553) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %556 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %557 = "llvm.load"(%556) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %558 = "llvm.xor"(%557, %554) : (i32, i32) -> i32
        "llvm.store"(%558, %556) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %561 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %562 = "llvm.load"(%561) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %563 = "llvm.shl"(%562, %11) : (i32, i32) -> i32
        %565 = "llvm.lshr"(%562, %252) : (i32, i32) -> i32
        %566 = "llvm.or"(%563, %565) : (i32, i32) -> i32
        %568 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%566, %568) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %571 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %572 = "llvm.load"(%571) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %574 = "llvm.getelementptr"(%47, %521) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %575 = "llvm.load"(%574) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %576 = "llvm.add"(%575, %572) : (i32, i32) -> i32
        "llvm.store"(%576, %574) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %579 = "llvm.getelementptr"(%47, %521) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %580 = "llvm.load"(%579) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %582 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %583 = "llvm.load"(%582) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %584 = "llvm.xor"(%583, %580) : (i32, i32) -> i32
        "llvm.store"(%584, %582) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %587 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %588 = "llvm.load"(%587) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %589 = "llvm.shl"(%588, %26) : (i32, i32) -> i32
        %591 = "llvm.lshr"(%588, %278) : (i32, i32) -> i32
        %592 = "llvm.or"(%589, %591) : (i32, i32) -> i32
        %594 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%592, %594) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %597 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %598 = "llvm.load"(%597) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %600 = "llvm.getelementptr"(%47, %547) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %601 = "llvm.load"(%600) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %602 = "llvm.add"(%601, %598) : (i32, i32) -> i32
        "llvm.store"(%602, %600) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %605 = "llvm.getelementptr"(%47, %547) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %606 = "llvm.load"(%605) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %608 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %609 = "llvm.load"(%608) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %610 = "llvm.xor"(%609, %606) : (i32, i32) -> i32
        "llvm.store"(%610, %608) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %613 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %614 = "llvm.load"(%613) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %615 = "llvm.shl"(%614, %36) : (i32, i32) -> i32
        %617 = "llvm.lshr"(%614, %304) : (i32, i32) -> i32
        %618 = "llvm.or"(%615, %617) : (i32, i32) -> i32
        %620 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%618, %620) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %623 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %624 = "llvm.load"(%623) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %626 = "llvm.getelementptr"(%47, %209) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %627 = "llvm.load"(%626) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %628 = "llvm.add"(%627, %624) : (i32, i32) -> i32
        "llvm.store"(%628, %626) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %631 = "llvm.getelementptr"(%47, %209) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %632 = "llvm.load"(%631) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %634 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %635 = "llvm.load"(%634) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %636 = "llvm.xor"(%635, %632) : (i32, i32) -> i32
        "llvm.store"(%636, %634) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %639 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %640 = "llvm.load"(%639) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %641 = "llvm.shl"(%640, %25) : (i32, i32) -> i32
        %643 = "llvm.lshr"(%640, %226) : (i32, i32) -> i32
        %644 = "llvm.or"(%641, %643) : (i32, i32) -> i32
        %646 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%644, %646) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %649 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %650 = "llvm.load"(%649) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %652 = "llvm.getelementptr"(%47, %443) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %653 = "llvm.load"(%652) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %654 = "llvm.add"(%653, %650) : (i32, i32) -> i32
        "llvm.store"(%654, %652) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %657 = "llvm.getelementptr"(%47, %443) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %658 = "llvm.load"(%657) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %660 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %661 = "llvm.load"(%660) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %662 = "llvm.xor"(%661, %658) : (i32, i32) -> i32
        "llvm.store"(%662, %660) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %665 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %666 = "llvm.load"(%665) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %667 = "llvm.shl"(%666, %11) : (i32, i32) -> i32
        %669 = "llvm.lshr"(%666, %252) : (i32, i32) -> i32
        %670 = "llvm.or"(%667, %669) : (i32, i32) -> i32
        %672 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%670, %672) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %675 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %676 = "llvm.load"(%675) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %678 = "llvm.getelementptr"(%47, %209) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %679 = "llvm.load"(%678) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %680 = "llvm.add"(%679, %676) : (i32, i32) -> i32
        "llvm.store"(%680, %678) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %683 = "llvm.getelementptr"(%47, %209) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %684 = "llvm.load"(%683) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %686 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %687 = "llvm.load"(%686) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %688 = "llvm.xor"(%687, %684) : (i32, i32) -> i32
        "llvm.store"(%688, %686) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %691 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %692 = "llvm.load"(%691) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %693 = "llvm.shl"(%692, %26) : (i32, i32) -> i32
        %695 = "llvm.lshr"(%692, %278) : (i32, i32) -> i32
        %696 = "llvm.or"(%693, %695) : (i32, i32) -> i32
        %698 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%696, %698) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %701 = "llvm.getelementptr"(%47, %529) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %702 = "llvm.load"(%701) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %704 = "llvm.getelementptr"(%47, %443) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %705 = "llvm.load"(%704) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %706 = "llvm.add"(%705, %702) : (i32, i32) -> i32
        "llvm.store"(%706, %704) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %709 = "llvm.getelementptr"(%47, %443) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %710 = "llvm.load"(%709) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %712 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %713 = "llvm.load"(%712) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %714 = "llvm.xor"(%713, %710) : (i32, i32) -> i32
        "llvm.store"(%714, %712) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %717 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %718 = "llvm.load"(%717) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %719 = "llvm.shl"(%718, %36) : (i32, i32) -> i32
        %721 = "llvm.lshr"(%718, %304) : (i32, i32) -> i32
        %722 = "llvm.or"(%719, %721) : (i32, i32) -> i32
        %724 = "llvm.getelementptr"(%47, %310) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%722, %724) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %727 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %728 = "llvm.load"(%727) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %730 = "llvm.getelementptr"(%47, %313) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %731 = "llvm.load"(%730) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %732 = "llvm.add"(%731, %728) : (i32, i32) -> i32
        "llvm.store"(%732, %730) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %735 = "llvm.getelementptr"(%47, %313) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %736 = "llvm.load"(%735) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %738 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %739 = "llvm.load"(%738) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %740 = "llvm.xor"(%739, %736) : (i32, i32) -> i32
        "llvm.store"(%740, %738) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %743 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %744 = "llvm.load"(%743) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %745 = "llvm.shl"(%744, %25) : (i32, i32) -> i32
        %747 = "llvm.lshr"(%744, %226) : (i32, i32) -> i32
        %748 = "llvm.or"(%745, %747) : (i32, i32) -> i32
        %750 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%748, %750) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %753 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %754 = "llvm.load"(%753) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %756 = "llvm.getelementptr"(%47, %547) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %757 = "llvm.load"(%756) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %758 = "llvm.add"(%757, %754) : (i32, i32) -> i32
        "llvm.store"(%758, %756) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %761 = "llvm.getelementptr"(%47, %547) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %762 = "llvm.load"(%761) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %764 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %765 = "llvm.load"(%764) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %766 = "llvm.xor"(%765, %762) : (i32, i32) -> i32
        "llvm.store"(%766, %764) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %769 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %770 = "llvm.load"(%769) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %771 = "llvm.shl"(%770, %11) : (i32, i32) -> i32
        %773 = "llvm.lshr"(%770, %252) : (i32, i32) -> i32
        %774 = "llvm.or"(%771, %773) : (i32, i32) -> i32
        %776 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%774, %776) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %779 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %780 = "llvm.load"(%779) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %782 = "llvm.getelementptr"(%47, %313) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %783 = "llvm.load"(%782) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %784 = "llvm.add"(%783, %780) : (i32, i32) -> i32
        "llvm.store"(%784, %782) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %787 = "llvm.getelementptr"(%47, %313) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %788 = "llvm.load"(%787) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %790 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %791 = "llvm.load"(%790) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %792 = "llvm.xor"(%791, %788) : (i32, i32) -> i32
        "llvm.store"(%792, %790) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %795 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %796 = "llvm.load"(%795) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %797 = "llvm.shl"(%796, %26) : (i32, i32) -> i32
        %799 = "llvm.lshr"(%796, %278) : (i32, i32) -> i32
        %800 = "llvm.or"(%797, %799) : (i32, i32) -> i32
        %802 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%800, %802) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %805 = "llvm.getelementptr"(%47, %217) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %806 = "llvm.load"(%805) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %808 = "llvm.getelementptr"(%47, %547) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %809 = "llvm.load"(%808) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %810 = "llvm.add"(%809, %806) : (i32, i32) -> i32
        "llvm.store"(%810, %808) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %813 = "llvm.getelementptr"(%47, %547) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %814 = "llvm.load"(%813) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %816 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %817 = "llvm.load"(%816) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %818 = "llvm.xor"(%817, %814) : (i32, i32) -> i32
        "llvm.store"(%818, %816) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %821 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %822 = "llvm.load"(%821) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %823 = "llvm.shl"(%822, %36) : (i32, i32) -> i32
        %825 = "llvm.lshr"(%822, %304) : (i32, i32) -> i32
        %826 = "llvm.or"(%823, %825) : (i32, i32) -> i32
        %828 = "llvm.getelementptr"(%47, %414) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%826, %828) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %831 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %832 = "llvm.load"(%831) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %834 = "llvm.getelementptr"(%47, %417) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %835 = "llvm.load"(%834) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %836 = "llvm.add"(%835, %832) : (i32, i32) -> i32
        "llvm.store"(%836, %834) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %839 = "llvm.getelementptr"(%47, %417) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %840 = "llvm.load"(%839) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %842 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %843 = "llvm.load"(%842) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %844 = "llvm.xor"(%843, %840) : (i32, i32) -> i32
        "llvm.store"(%844, %842) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %847 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %848 = "llvm.load"(%847) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %849 = "llvm.shl"(%848, %25) : (i32, i32) -> i32
        %851 = "llvm.lshr"(%848, %226) : (i32, i32) -> i32
        %852 = "llvm.or"(%849, %851) : (i32, i32) -> i32
        %854 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%852, %854) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %857 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %858 = "llvm.load"(%857) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %860 = "llvm.getelementptr"(%47, %235) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %861 = "llvm.load"(%860) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %862 = "llvm.add"(%861, %858) : (i32, i32) -> i32
        "llvm.store"(%862, %860) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %865 = "llvm.getelementptr"(%47, %235) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %866 = "llvm.load"(%865) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %868 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %869 = "llvm.load"(%868) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %870 = "llvm.xor"(%869, %866) : (i32, i32) -> i32
        "llvm.store"(%870, %868) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %873 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %874 = "llvm.load"(%873) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %875 = "llvm.shl"(%874, %11) : (i32, i32) -> i32
        %877 = "llvm.lshr"(%874, %252) : (i32, i32) -> i32
        %878 = "llvm.or"(%875, %877) : (i32, i32) -> i32
        %880 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%878, %880) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %883 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %884 = "llvm.load"(%883) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %886 = "llvm.getelementptr"(%47, %417) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %887 = "llvm.load"(%886) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %888 = "llvm.add"(%887, %884) : (i32, i32) -> i32
        "llvm.store"(%888, %886) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %891 = "llvm.getelementptr"(%47, %417) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %892 = "llvm.load"(%891) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %894 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %895 = "llvm.load"(%894) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %896 = "llvm.xor"(%895, %892) : (i32, i32) -> i32
        "llvm.store"(%896, %894) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %899 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %900 = "llvm.load"(%899) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %901 = "llvm.shl"(%900, %26) : (i32, i32) -> i32
        %903 = "llvm.lshr"(%900, %278) : (i32, i32) -> i32
        %904 = "llvm.or"(%901, %903) : (i32, i32) -> i32
        %906 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%904, %906) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %909 = "llvm.getelementptr"(%47, %321) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %910 = "llvm.load"(%909) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %912 = "llvm.getelementptr"(%47, %235) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %913 = "llvm.load"(%912) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %914 = "llvm.add"(%913, %910) : (i32, i32) -> i32
        "llvm.store"(%914, %912) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %917 = "llvm.getelementptr"(%47, %235) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %918 = "llvm.load"(%917) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %920 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %921 = "llvm.load"(%920) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %922 = "llvm.xor"(%921, %918) : (i32, i32) -> i32
        "llvm.store"(%922, %920) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %925 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %926 = "llvm.load"(%925) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %927 = "llvm.shl"(%926, %36) : (i32, i32) -> i32
        %929 = "llvm.lshr"(%926, %304) : (i32, i32) -> i32
        %930 = "llvm.or"(%927, %929) : (i32, i32) -> i32
        %932 = "llvm.getelementptr"(%47, %518) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%930, %932) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %935 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %936 = "llvm.load"(%935) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %938 = "llvm.getelementptr"(%47, %521) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %939 = "llvm.load"(%938) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %940 = "llvm.add"(%939, %936) : (i32, i32) -> i32
        "llvm.store"(%940, %938) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %943 = "llvm.getelementptr"(%47, %521) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %944 = "llvm.load"(%943) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %946 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %947 = "llvm.load"(%946) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %948 = "llvm.xor"(%947, %944) : (i32, i32) -> i32
        "llvm.store"(%948, %946) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %951 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %952 = "llvm.load"(%951) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %953 = "llvm.shl"(%952, %25) : (i32, i32) -> i32
        %955 = "llvm.lshr"(%952, %226) : (i32, i32) -> i32
        %956 = "llvm.or"(%953, %955) : (i32, i32) -> i32
        %958 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%956, %958) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %961 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %962 = "llvm.load"(%961) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %964 = "llvm.getelementptr"(%47, %339) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %965 = "llvm.load"(%964) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %966 = "llvm.add"(%965, %962) : (i32, i32) -> i32
        "llvm.store"(%966, %964) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %969 = "llvm.getelementptr"(%47, %339) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %970 = "llvm.load"(%969) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %972 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %973 = "llvm.load"(%972) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %974 = "llvm.xor"(%973, %970) : (i32, i32) -> i32
        "llvm.store"(%974, %972) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %977 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %978 = "llvm.load"(%977) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %979 = "llvm.shl"(%978, %11) : (i32, i32) -> i32
        %981 = "llvm.lshr"(%978, %252) : (i32, i32) -> i32
        %982 = "llvm.or"(%979, %981) : (i32, i32) -> i32
        %984 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%982, %984) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %987 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %988 = "llvm.load"(%987) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %990 = "llvm.getelementptr"(%47, %521) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %991 = "llvm.load"(%990) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %992 = "llvm.add"(%991, %988) : (i32, i32) -> i32
        "llvm.store"(%992, %990) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %995 = "llvm.getelementptr"(%47, %521) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %996 = "llvm.load"(%995) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %998 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %999 = "llvm.load"(%998) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1000 = "llvm.xor"(%999, %996) : (i32, i32) -> i32
        "llvm.store"(%1000, %998) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %1003 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %1004 = "llvm.load"(%1003) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1005 = "llvm.shl"(%1004, %26) : (i32, i32) -> i32
        %1007 = "llvm.lshr"(%1004, %278) : (i32, i32) -> i32
        %1008 = "llvm.or"(%1005, %1007) : (i32, i32) -> i32
        %1010 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%1008, %1010) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %1013 = "llvm.getelementptr"(%47, %425) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %1014 = "llvm.load"(%1013) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1016 = "llvm.getelementptr"(%47, %339) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %1017 = "llvm.load"(%1016) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1018 = "llvm.add"(%1017, %1014) : (i32, i32) -> i32
        "llvm.store"(%1018, %1016) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %1021 = "llvm.getelementptr"(%47, %339) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %1022 = "llvm.load"(%1021) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1024 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %1025 = "llvm.load"(%1024) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1026 = "llvm.xor"(%1025, %1022) : (i32, i32) -> i32
        "llvm.store"(%1026, %1024) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %1029 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %1030 = "llvm.load"(%1029) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1031 = "llvm.shl"(%1030, %36) : (i32, i32) -> i32
        %1033 = "llvm.lshr"(%1030, %304) : (i32, i32) -> i32
        %1034 = "llvm.or"(%1031, %1033) : (i32, i32) -> i32
        %1036 = "llvm.getelementptr"(%47, %206) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%1034, %1036) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %1038 = "llvm.add"(%arg200_0, %8) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%1038) [^200] : (i32) -> ()
      ^204():
        "llvm.br"(%9) [^1040] : (i32) -> ()
      ^1040(%arg1040_0 : i32):
        %1042 = "llvm.icmp"(%arg1040_0, %25) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%1042) [^1043, ^1044] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^1043():
        %1046 = "llvm.mul"(%35, %arg1040_0) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %1047 = "llvm.sext"(%1046) : (i32) -> i64
        %1048 = "llvm.getelementptr"(%48, %1047) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %1049 = "llvm.sext"(%arg1040_0) : (i32) -> i64
        %1050 = "llvm.getelementptr"(%47, %12, %1049) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %1051 = "llvm.load"(%1050) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1053 = "llvm.getelementptr"(%46, %12, %1049) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %1054 = "llvm.load"(%1053) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %1055 = "llvm.add"(%1051, %1054) : (i32, i32) -> i32
        %1056 = "llvm.trunc"(%1055) : (i32) -> i8
        "llvm.store"(%1056, %1048) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %1058 = "llvm.lshr"(%1055, %26) : (i32, i32) -> i32
        %1059 = "llvm.trunc"(%1058) : (i32) -> i8
        %1060 = "llvm.getelementptr"(%1048, %17) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%1059, %1060) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %1062 = "llvm.lshr"(%1055, %25) : (i32, i32) -> i32
        %1063 = "llvm.trunc"(%1062) : (i32) -> i8
        %1064 = "llvm.getelementptr"(%1048, %19) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%1063, %1064) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %1066 = "llvm.lshr"(%1055, %24) : (i32, i32) -> i32
        %1067 = "llvm.trunc"(%1066) : (i32) -> i8
        %1068 = "llvm.getelementptr"(%1048, %21) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%1067, %1068) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %1070 = "llvm.add"(%arg1040_0, %8) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%1070) [^1040] : (i32) -> ()
      ^1044():
        %1072 = "llvm.add"(%arg107_0, %8) : (i32, i32) -> i32
        %1073 = "llvm.sub"(%23, %arg107_1) : (i64, i64) -> i64
        %1074 = "llvm.icmp"(%1073, %34) <{"predicate" = 8 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%1074, %1073) [^1075, ^1076] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
      ^1075():
        "llvm.br"(%34) [^1076] : (i64) -> ()
      ^1076(%arg1076_0 : i64):
        "llvm.br"(%12) [^1079] : (i64) -> ()
      ^1079(%arg1079_0 : i64):
        %1081 = "llvm.icmp"(%arg1079_0, %arg1076_0) <{"predicate" = 6 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%1081) [^1082, ^1083] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^1082():
        %1085 = "llvm.add"(%arg107_1, %arg1079_0) : (i64, i64) -> i64
        %1086 = "llvm.getelementptr"(%105, %1085) <{"elem_type" = i8, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %1087 = "llvm.load"(%1086) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %1088 = "llvm.zext"(%1087) : (i8) -> i32
        %1089 = "llvm.getelementptr"(%48, %12, %arg1079_0) <{"elem_type" = !llvm.array<64 x i8>, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %1090 = "llvm.load"(%1089) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %1091 = "llvm.zext"(%1090) : (i8) -> i32
        %1092 = "llvm.xor"(%1088, %1091) : (i32, i32) -> i32
        %1093 = "llvm.trunc"(%1092) : (i32) -> i8
        %1095 = "llvm.getelementptr"(%106, %1085) <{"elem_type" = i8, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%1093, %1095) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %1097 = "llvm.add"(%arg1079_0, %17) : (i64, i64) -> i64
        "llvm.br"(%1097) [^1079] : (i64) -> ()
      ^1083():
        %1099 = "llvm.add"(%arg107_1, %arg1076_0) : (i64, i64) -> i64
        "llvm.br"(%1072, %1099) [^107] : (i32, i64) -> ()
      ^111():
        %1101 = "llvm.getelementptr"(%52, %12, %12) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %1102 = "llvm.load"(%1101) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %1103 = "llvm.zext"(%1102) : (i8) -> i32
        %1104 = "llvm.shl"(%1103, %24) : (i32, i32) -> i32
        %1105 = "llvm.getelementptr"(%52, %12, %17) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %1106 = "llvm.load"(%1105) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %1107 = "llvm.zext"(%1106) : (i8) -> i32
        %1108 = "llvm.shl"(%1107, %25) : (i32, i32) -> i32
        %1109 = "llvm.or"(%1104, %1108) : (i32, i32) -> i32
        %1110 = "llvm.getelementptr"(%52, %12, %19) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %1111 = "llvm.load"(%1110) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %1112 = "llvm.zext"(%1111) : (i8) -> i32
        %1113 = "llvm.shl"(%1112, %26) : (i32, i32) -> i32
        %1114 = "llvm.or"(%1109, %1113) : (i32, i32) -> i32
        %1115 = "llvm.getelementptr"(%52, %12, %21) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        %1116 = "llvm.load"(%1115) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %1117 = "llvm.zext"(%1116) : (i8) -> i32
        %1118 = "llvm.or"(%1114, %1117) : (i32, i32) -> i32
        "llvm.return"(%1118) : (i32) -> ()
    }) : () -> ()
}) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "o", "dlti.legal_int_widths" = array<i32: 32, 64>, "dlti.stack_alignment" = 128 : i64, "dlti.function_pointer_alignment" = #dlti.function_pointer_alignment<32, function_dependent = true>>, "llvm.ident" = "Homebrew clang version 22.1.7", "llvm.module_asm" = [], "llvm.target_triple" = "arm64-apple-macosx26.0.0"} : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^[[bb4:[0-9]+]]():
// CHECK-NEXT:     "llvm.module_flags"() {{.*}} : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}"sym_name" = "chacha20"{{.*}}}> ({
// CHECK-NEXT:       ^[[bb7:[0-9]+]]():
// CHECK-NEXT:         %[[v8:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v9:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         %[[v10:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
// CHECK-NEXT:         %[[v11:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK-NEXT:         %[[v1953:[0-9]+]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v1954:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1953]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v1951:[0-9]+]] = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v1952:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1951]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v14:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 74 : i8}> : () -> i8
// CHECK-NEXT:         %[[v15:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 114 : i32}> : () -> i32
// CHECK-NEXT:         %[[v16:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 76 : i8}> : () -> i8
// CHECK-NEXT:         %[[v1949:[0-9]+]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v1950:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1949]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v18:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 97 : i8}> : () -> i8
// CHECK-NEXT:         %[[v1947:[0-9]+]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v1948:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1947]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v20:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 100 : i8}> : () -> i8
// CHECK-NEXT:         %[[v1945:[0-9]+]] = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v1946:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1945]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v22:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 105 : i8}> : () -> i8
// CHECK-NEXT:         %[[v1943:[0-9]+]] = "riscv.li"() <{"value" = 114 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v24:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 24 : i32}> : () -> i32
// CHECK-NEXT:         %[[v25:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
// CHECK-NEXT:         %[[v26:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
// CHECK-NEXT:         %[[v27:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1634760805 : i32}> : () -> i32
// CHECK-NEXT:         %[[v28:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 857760878 : i32}> : () -> i32
// CHECK-NEXT:         %[[v29:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2036477234 : i32}> : () -> i32
// CHECK-NEXT:         %[[v30:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1797285236 : i32}> : () -> i32
// CHECK-NEXT:         %[[v1941:[0-9]+]] = "riscv.li"() <{"value" = 12 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v1942:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1941]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v32:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:         %[[v33:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
// CHECK-NEXT:         %[[v1939:[0-9]+]] = "riscv.li"() <{"value" = 64 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v35:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
// CHECK-NEXT:         %[[v36:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:         %[[v37:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK-NEXT:         %[[v38:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:         %[[v39:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 9 : i32}> : () -> i32
// CHECK-NEXT:         %[[v40:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
// CHECK-NEXT:         %[[v41:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// CHECK-NEXT:         %[[v42:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 14 : i32}> : () -> i32
// CHECK-NEXT:         %[[v43:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
// CHECK-NEXT:         %[[v44:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
// CHECK-NEXT:         %[[v45:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i8}> : () -> i8
// CHECK-NEXT:         %[[v46:[0-9]+]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 4 : i64, "elem_type" = !llvm.array<16 x i32>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v47:[0-9]+]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 4 : i64, "elem_type" = !llvm.array<16 x i32>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v48:[0-9]+]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<64 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v49:[0-9]+]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<32 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v50:[0-9]+]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<12 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v51:[0-9]+]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<114 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v52:[0-9]+]] = "llvm.alloca"(%[[v8]]) <{"alignment" = 1 : i64, "elem_type" = !llvm.array<114 x i8>}> : (i32) -> !llvm.ptr
// CHECK-NEXT:         %[[v977:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v977]]) [^[[bb53:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb53]](%[[varg53_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v979:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg53_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v55:[0-9]+]] = "llvm.icmp"(%[[v979]], %[[v10]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         %[[v980:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v55]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v980]]) [^[[bb56:[0-9]+]], ^[[bb57:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb56]]():
// CHECK-NEXT:         %[[v1937:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v979]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1938:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1937]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v1934:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v979]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1935:[0-9]+]] = "riscv.sextw"(%[[v1934]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1936:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1935]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v61:[0-9]+]] = "llvm.getelementptr"(%[[v49]], %[[v1954]], %[[v1936]]) <{"elem_type" = !llvm.array<32 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1938]], %[[v61]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb63:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb63]]():
// CHECK-NEXT:         %[[v65:[0-9]+]] = "llvm.add"(%[[v979]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v975:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v65]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v975]]) [^[[bb53]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb57]]():
// CHECK-NEXT:         %[[v922:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v922]]) [^[[bb67:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb67]](%[[varg67_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v924:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg67_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v69:[0-9]+]] = "llvm.icmp"(%[[v924]], %[[v11]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         %[[v927:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v69]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v927]]) [^[[bb70:[0-9]+]], ^[[bb71:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb70]]():
// CHECK-NEXT:         %[[v1931:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v924]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1932:[0-9]+]] = "riscv.sextw"(%[[v1931]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1933:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1932]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v74:[0-9]+]] = "llvm.getelementptr"(%[[v50]], %[[v1954]], %[[v1933]]) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v45]], %[[v74]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb76:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb76]]():
// CHECK-NEXT:         %[[v78:[0-9]+]] = "llvm.add"(%[[v924]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v920:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v78]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v920]]) [^[[bb67]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb71]]():
// CHECK-NEXT:         %[[v80:[0-9]+]] = "llvm.getelementptr"(%[[v50]], %[[v1954]], %[[v1952]]) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v14]], %[[v80]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v939:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v939]]) [^[[bb82:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb82]](%[[varg82_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v941:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg82_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v84:[0-9]+]] = "llvm.icmp"(%[[v941]], %[[v15]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         %[[v942:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v84]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v942]]) [^[[bb85:[0-9]+]], ^[[bb86:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb85]]():
// CHECK-NEXT:         %[[v1928:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v941]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1929:[0-9]+]] = "riscv.sextw"(%[[v1928]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1930:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1929]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v89:[0-9]+]] = "llvm.getelementptr"(%[[v51]], %[[v1954]], %[[v1930]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v45]], %[[v89]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb91:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb91]]():
// CHECK-NEXT:         %[[v93:[0-9]+]] = "llvm.add"(%[[v941]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v937:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v93]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v937]]) [^[[bb82]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb86]]():
// CHECK-NEXT:         %[[v95:[0-9]+]] = "llvm.getelementptr"(%[[v51]], %[[v1954]], %[[v1954]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v16]], %[[v95]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v97:[0-9]+]] = "llvm.getelementptr"(%[[v51]], %[[v1954]], %[[v1950]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v18]], %[[v97]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v99:[0-9]+]] = "llvm.getelementptr"(%[[v51]], %[[v1954]], %[[v1948]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v20]], %[[v99]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v101:[0-9]+]] = "llvm.getelementptr"(%[[v51]], %[[v1954]], %[[v1946]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v22]], %[[v101]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v103:[0-9]+]] = "llvm.getelementptr"(%[[v49]], %[[v1954]], %[[v1954]]) <{"elem_type" = !llvm.array<32 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v104:[0-9]+]] = "llvm.getelementptr"(%[[v50]], %[[v1954]], %[[v1954]]) <{"elem_type" = !llvm.array<12 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v105:[0-9]+]] = "llvm.getelementptr"(%[[v51]], %[[v1954]], %[[v1954]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v106:[0-9]+]] = "llvm.getelementptr"(%[[v52]], %[[v1954]], %[[v1954]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v966:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v8]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v966]], %[[v1953]]) [^[[bb107:[0-9]+]]] : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb107]](%[[varg107_0:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg107_1:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v969:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg107_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1926:[0-9]+]] = "riscv.sltu"(%[[varg107_1]], %[[v1943]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1927:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1926]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v973:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1927]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v973]]) [^[[bb110:[0-9]+]], ^[[bb111:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb110]]():
// CHECK-NEXT:         "llvm.store"(%[[v27]], %[[v46]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v114:[0-9]+]] = "llvm.getelementptr"(%[[v46]], %[[v1954]], %[[v1950]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v28]], %[[v114]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v116:[0-9]+]] = "llvm.getelementptr"(%[[v46]], %[[v1954]], %[[v1948]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v29]], %[[v116]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v118:[0-9]+]] = "llvm.getelementptr"(%[[v46]], %[[v1954]], %[[v1946]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v30]], %[[v118]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v984:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v984]]) [^[[bb120:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb120]](%[[varg120_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v986:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg120_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v122:[0-9]+]] = "llvm.icmp"(%[[v986]], %[[v26]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         %[[v992:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v122]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v992]]) [^[[bb123:[0-9]+]], ^[[bb124:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb123]]():
// CHECK-NEXT:         %[[v126:[0-9]+]] = "llvm.mul"(%[[v35]], %[[v986]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1921:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v126]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1922:[0-9]+]] = "riscv.sextw"(%[[v1921]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1917:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v103]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1919:[0-9]+]] = "riscv.add"(%[[v1917]], %[[v1922]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1920:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1919]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v129:[0-9]+]] = "llvm.load"(%[[v1920]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v130:[0-9]+]] = "llvm.zext"(%[[v129]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1913:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1920]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1915:[0-9]+]] = "riscv.add"(%[[v1913]], %[[v1949]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1916:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1915]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v132:[0-9]+]] = "llvm.load"(%[[v1916]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v133:[0-9]+]] = "llvm.zext"(%[[v132]]) : (i8) -> i32
// CHECK-NEXT:         %[[v134:[0-9]+]] = "llvm.shl"(%[[v133]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v135:[0-9]+]] = "llvm.or"(%[[v130]], %[[v134]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1909:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1920]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1911:[0-9]+]] = "riscv.add"(%[[v1909]], %[[v1947]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1912:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1911]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v137:[0-9]+]] = "llvm.load"(%[[v1912]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v138:[0-9]+]] = "llvm.zext"(%[[v137]]) : (i8) -> i32
// CHECK-NEXT:         %[[v139:[0-9]+]] = "llvm.shl"(%[[v138]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v140:[0-9]+]] = "llvm.or"(%[[v135]], %[[v139]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1905:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1920]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1907:[0-9]+]] = "riscv.add"(%[[v1905]], %[[v1945]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1908:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1907]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v142:[0-9]+]] = "llvm.load"(%[[v1908]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v143:[0-9]+]] = "llvm.zext"(%[[v142]]) : (i8) -> i32
// CHECK-NEXT:         %[[v144:[0-9]+]] = "llvm.shl"(%[[v143]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v145:[0-9]+]] = "llvm.or"(%[[v140]], %[[v144]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v146:[0-9]+]] = "llvm.add"(%[[v35]], %[[v986]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1902:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v146]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1903:[0-9]+]] = "riscv.sextw"(%[[v1902]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1904:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1903]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v148:[0-9]+]] = "llvm.getelementptr"(%[[v46]], %[[v1954]], %[[v1904]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v145]], %[[v148]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v150:[0-9]+]] = "llvm.add"(%[[v986]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v982:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v150]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v982]]) [^[[bb120]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb124]]():
// CHECK-NEXT:         %[[v152:[0-9]+]] = "llvm.getelementptr"(%[[v46]], %[[v1954]], %[[v1942]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v969]], %[[v152]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v946:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v946]]) [^[[bb154:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb154]](%[[varg154_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v948:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg154_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v156:[0-9]+]] = "llvm.icmp"(%[[v948]], %[[v32]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         %[[v950:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v156]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v950]]) [^[[bb157:[0-9]+]], ^[[bb158:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb157]]():
// CHECK-NEXT:         %[[v160:[0-9]+]] = "llvm.mul"(%[[v35]], %[[v948]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1899:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v160]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1900:[0-9]+]] = "riscv.sextw"(%[[v1899]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1895:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v104]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1897:[0-9]+]] = "riscv.add"(%[[v1895]], %[[v1900]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1898:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1897]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v163:[0-9]+]] = "llvm.load"(%[[v1898]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v164:[0-9]+]] = "llvm.zext"(%[[v163]]) : (i8) -> i32
// CHECK-NEXT:         %[[v1891:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1898]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1893:[0-9]+]] = "riscv.add"(%[[v1891]], %[[v1949]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1894:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1893]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v166:[0-9]+]] = "llvm.load"(%[[v1894]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v167:[0-9]+]] = "llvm.zext"(%[[v166]]) : (i8) -> i32
// CHECK-NEXT:         %[[v168:[0-9]+]] = "llvm.shl"(%[[v167]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v169:[0-9]+]] = "llvm.or"(%[[v164]], %[[v168]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1887:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1898]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1889:[0-9]+]] = "riscv.add"(%[[v1887]], %[[v1947]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1890:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1889]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v171:[0-9]+]] = "llvm.load"(%[[v1890]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v172:[0-9]+]] = "llvm.zext"(%[[v171]]) : (i8) -> i32
// CHECK-NEXT:         %[[v173:[0-9]+]] = "llvm.shl"(%[[v172]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v174:[0-9]+]] = "llvm.or"(%[[v169]], %[[v173]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1883:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1898]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1885:[0-9]+]] = "riscv.add"(%[[v1883]], %[[v1945]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1886:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1885]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v176:[0-9]+]] = "llvm.load"(%[[v1886]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v177:[0-9]+]] = "llvm.zext"(%[[v176]]) : (i8) -> i32
// CHECK-NEXT:         %[[v178:[0-9]+]] = "llvm.shl"(%[[v177]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v179:[0-9]+]] = "llvm.or"(%[[v174]], %[[v178]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v180:[0-9]+]] = "llvm.add"(%[[v38]], %[[v948]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1880:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v180]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1881:[0-9]+]] = "riscv.sextw"(%[[v1880]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1882:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1881]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v182:[0-9]+]] = "llvm.getelementptr"(%[[v46]], %[[v1954]], %[[v1882]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v179]], %[[v182]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v184:[0-9]+]] = "llvm.add"(%[[v948]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v944:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v184]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v944]]) [^[[bb154]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb158]]():
// CHECK-NEXT:         %[[v989:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v989]]) [^[[bb186:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb186]](%[[varg186_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v991:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg186_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v188:[0-9]+]] = "llvm.icmp"(%[[v991]], %[[v25]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         %[[v994:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v188]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v994]]) [^[[bb189:[0-9]+]], ^[[bb190:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb189]]():
// CHECK-NEXT:         %[[v1877:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v991]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1878:[0-9]+]] = "riscv.sextw"(%[[v1877]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1879:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1878]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v193:[0-9]+]] = "llvm.getelementptr"(%[[v46]], %[[v1954]], %[[v1879]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v194:[0-9]+]] = "llvm.load"(%[[v193]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v195:[0-9]+]] = "llvm.getelementptr"(%[[v47]], %[[v1954]], %[[v1879]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v194]], %[[v195]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v197:[0-9]+]] = "llvm.add"(%[[v991]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v987:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v197]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v987]]) [^[[bb186]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb190]]():
// CHECK-NEXT:         %[[v931:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v931]]) [^[[bb199:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb199]](%[[varg199_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v933:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg199_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v201:[0-9]+]] = "llvm.icmp"(%[[v933]], %[[v33]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         %[[v934:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v201]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v934]]) [^[[bb202:[0-9]+]], ^[[bb203:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb202]]():
// CHECK-NEXT:         %[[v1874:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v35]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1875:[0-9]+]] = "riscv.sextw"(%[[v1874]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1870:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1872:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1870]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1873:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1872]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v207:[0-9]+]] = "llvm.load"(%[[v1873]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1867:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1868:[0-9]+]] = "riscv.sextw"(%[[v1867]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1863:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1865:[0-9]+]] = "riscv.sh2add"(%[[v1868]], %[[v1863]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1866:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1865]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v210:[0-9]+]] = "llvm.load"(%[[v1866]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v211:[0-9]+]] = "llvm.add"(%[[v210]], %[[v207]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v211]], %[[v1866]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1859:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1861:[0-9]+]] = "riscv.sh2add"(%[[v1868]], %[[v1859]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1862:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1861]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v214:[0-9]+]] = "llvm.load"(%[[v1862]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1856:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v11]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1857:[0-9]+]] = "riscv.sextw"(%[[v1856]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1852:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1854:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1852]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1855:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1854]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v217:[0-9]+]] = "llvm.load"(%[[v1855]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v218:[0-9]+]] = "llvm.xor"(%[[v217]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v218]], %[[v1855]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1848:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1850:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1848]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1851:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1850]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v221:[0-9]+]] = "llvm.load"(%[[v1851]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v222:[0-9]+]] = "llvm.shl"(%[[v221]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v223:[0-9]+]] = "llvm.sub"(%[[v10]], %[[v25]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v224:[0-9]+]] = "llvm.lshr"(%[[v221]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v225:[0-9]+]] = "llvm.or"(%[[v222]], %[[v224]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1844:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1846:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1844]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1847:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1846]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v225]], %[[v1847]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1840:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1842:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1840]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1843:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1842]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v229:[0-9]+]] = "llvm.load"(%[[v1843]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1837:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v26]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1838:[0-9]+]] = "riscv.sextw"(%[[v1837]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1833:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1835:[0-9]+]] = "riscv.sh2add"(%[[v1838]], %[[v1833]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1836:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1835]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v232:[0-9]+]] = "llvm.load"(%[[v1836]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v233:[0-9]+]] = "llvm.add"(%[[v232]], %[[v229]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v233]], %[[v1836]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1829:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1831:[0-9]+]] = "riscv.sh2add"(%[[v1838]], %[[v1829]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1832:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1831]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v236:[0-9]+]] = "llvm.load"(%[[v1832]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1825:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1827:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1825]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1828:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1827]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v238:[0-9]+]] = "llvm.load"(%[[v1828]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v239:[0-9]+]] = "llvm.xor"(%[[v238]], %[[v236]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v239]], %[[v1828]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1821:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1823:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1821]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1824:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1823]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v242:[0-9]+]] = "llvm.load"(%[[v1824]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v243:[0-9]+]] = "llvm.shl"(%[[v242]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v244:[0-9]+]] = "llvm.sub"(%[[v10]], %[[v11]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v245:[0-9]+]] = "llvm.lshr"(%[[v242]], %[[v244]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v246:[0-9]+]] = "llvm.or"(%[[v243]], %[[v245]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1817:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1819:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1817]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1820:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1819]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v246]], %[[v1820]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1813:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1815:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1813]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1816:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1815]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v250:[0-9]+]] = "llvm.load"(%[[v1816]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1809:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1811:[0-9]+]] = "riscv.sh2add"(%[[v1868]], %[[v1809]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1812:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1811]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v252:[0-9]+]] = "llvm.load"(%[[v1812]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v253:[0-9]+]] = "llvm.add"(%[[v252]], %[[v250]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v253]], %[[v1812]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1805:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1807:[0-9]+]] = "riscv.sh2add"(%[[v1868]], %[[v1805]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1808:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1807]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v256:[0-9]+]] = "llvm.load"(%[[v1808]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1801:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1803:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1801]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1804:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1803]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v258:[0-9]+]] = "llvm.load"(%[[v1804]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v259:[0-9]+]] = "llvm.xor"(%[[v258]], %[[v256]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v259]], %[[v1804]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1797:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1799:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1797]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1800:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1799]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v262:[0-9]+]] = "llvm.load"(%[[v1800]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v263:[0-9]+]] = "llvm.shl"(%[[v262]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v264:[0-9]+]] = "llvm.sub"(%[[v10]], %[[v26]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v265:[0-9]+]] = "llvm.lshr"(%[[v262]], %[[v264]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v266:[0-9]+]] = "llvm.or"(%[[v263]], %[[v265]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1793:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1795:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1793]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1796:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1795]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v266]], %[[v1796]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1789:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1791:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1789]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1792:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1791]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v270:[0-9]+]] = "llvm.load"(%[[v1792]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1785:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1787:[0-9]+]] = "riscv.sh2add"(%[[v1838]], %[[v1785]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1788:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1787]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v272:[0-9]+]] = "llvm.load"(%[[v1788]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v273:[0-9]+]] = "llvm.add"(%[[v272]], %[[v270]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v273]], %[[v1788]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1781:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1783:[0-9]+]] = "riscv.sh2add"(%[[v1838]], %[[v1781]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1784:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1783]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v276:[0-9]+]] = "llvm.load"(%[[v1784]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1777:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1779:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1777]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1780:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1779]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v278:[0-9]+]] = "llvm.load"(%[[v1780]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v279:[0-9]+]] = "llvm.xor"(%[[v278]], %[[v276]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v279]], %[[v1780]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1773:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1775:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1773]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1776:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1775]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v282:[0-9]+]] = "llvm.load"(%[[v1776]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v283:[0-9]+]] = "llvm.shl"(%[[v282]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v284:[0-9]+]] = "llvm.sub"(%[[v10]], %[[v36]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v285:[0-9]+]] = "llvm.lshr"(%[[v282]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v286:[0-9]+]] = "llvm.or"(%[[v283]], %[[v285]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1769:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1771:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1769]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1772:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1771]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v286]], %[[v1772]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1766:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v37]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1767:[0-9]+]] = "riscv.sextw"(%[[v1766]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1762:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1764:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1762]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1765:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1764]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v291:[0-9]+]] = "llvm.load"(%[[v1765]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1759:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v8]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1760:[0-9]+]] = "riscv.sextw"(%[[v1759]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1755:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1757:[0-9]+]] = "riscv.sh2add"(%[[v1760]], %[[v1755]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1758:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1757]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v294:[0-9]+]] = "llvm.load"(%[[v1758]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v295:[0-9]+]] = "llvm.add"(%[[v294]], %[[v291]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v295]], %[[v1758]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1751:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1753:[0-9]+]] = "riscv.sh2add"(%[[v1760]], %[[v1751]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1754:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1753]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v298:[0-9]+]] = "llvm.load"(%[[v1754]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1748:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v38]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1749:[0-9]+]] = "riscv.sextw"(%[[v1748]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1744:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1746:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1744]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1747:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1746]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v301:[0-9]+]] = "llvm.load"(%[[v1747]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v302:[0-9]+]] = "llvm.xor"(%[[v301]], %[[v298]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v302]], %[[v1747]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1740:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1742:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1740]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1743:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1742]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v305:[0-9]+]] = "llvm.load"(%[[v1743]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v306:[0-9]+]] = "llvm.shl"(%[[v305]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v307:[0-9]+]] = "llvm.lshr"(%[[v305]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v308:[0-9]+]] = "llvm.or"(%[[v306]], %[[v307]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1736:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1738:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1736]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1739:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1738]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v308]], %[[v1739]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1732:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1734:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1732]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1735:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1734]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v312:[0-9]+]] = "llvm.load"(%[[v1735]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1729:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v39]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1730:[0-9]+]] = "riscv.sextw"(%[[v1729]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1725:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1727:[0-9]+]] = "riscv.sh2add"(%[[v1730]], %[[v1725]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1728:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1727]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v315:[0-9]+]] = "llvm.load"(%[[v1728]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v316:[0-9]+]] = "llvm.add"(%[[v315]], %[[v312]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v316]], %[[v1728]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1721:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1723:[0-9]+]] = "riscv.sh2add"(%[[v1730]], %[[v1721]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1724:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1723]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v319:[0-9]+]] = "llvm.load"(%[[v1724]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1717:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1719:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1717]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1720:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1719]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v321:[0-9]+]] = "llvm.load"(%[[v1720]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v322:[0-9]+]] = "llvm.xor"(%[[v321]], %[[v319]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v322]], %[[v1720]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1713:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1715:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1713]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1716:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1715]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v325:[0-9]+]] = "llvm.load"(%[[v1716]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v326:[0-9]+]] = "llvm.shl"(%[[v325]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v327:[0-9]+]] = "llvm.lshr"(%[[v325]], %[[v244]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v328:[0-9]+]] = "llvm.or"(%[[v326]], %[[v327]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1709:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1711:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1709]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1712:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1711]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v328]], %[[v1712]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1705:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1707:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1705]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1708:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1707]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v332:[0-9]+]] = "llvm.load"(%[[v1708]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1701:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1703:[0-9]+]] = "riscv.sh2add"(%[[v1760]], %[[v1701]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1704:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1703]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v334:[0-9]+]] = "llvm.load"(%[[v1704]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v335:[0-9]+]] = "llvm.add"(%[[v334]], %[[v332]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v335]], %[[v1704]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1697:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1699:[0-9]+]] = "riscv.sh2add"(%[[v1760]], %[[v1697]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1700:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1699]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v338:[0-9]+]] = "llvm.load"(%[[v1700]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1693:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1695:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1693]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1696:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1695]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v340:[0-9]+]] = "llvm.load"(%[[v1696]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v341:[0-9]+]] = "llvm.xor"(%[[v340]], %[[v338]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v341]], %[[v1696]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1689:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1691:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1689]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1692:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1691]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v344:[0-9]+]] = "llvm.load"(%[[v1692]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v345:[0-9]+]] = "llvm.shl"(%[[v344]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v346:[0-9]+]] = "llvm.lshr"(%[[v344]], %[[v264]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v347:[0-9]+]] = "llvm.or"(%[[v345]], %[[v346]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1685:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1687:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1685]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1688:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1687]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v347]], %[[v1688]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1681:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1683:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1681]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1684:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1683]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v351:[0-9]+]] = "llvm.load"(%[[v1684]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1677:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1679:[0-9]+]] = "riscv.sh2add"(%[[v1730]], %[[v1677]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1680:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1679]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v353:[0-9]+]] = "llvm.load"(%[[v1680]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v354:[0-9]+]] = "llvm.add"(%[[v353]], %[[v351]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v354]], %[[v1680]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1673:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1675:[0-9]+]] = "riscv.sh2add"(%[[v1730]], %[[v1673]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1676:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1675]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v357:[0-9]+]] = "llvm.load"(%[[v1676]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1669:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1671:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1669]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1672:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1671]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v359:[0-9]+]] = "llvm.load"(%[[v1672]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v360:[0-9]+]] = "llvm.xor"(%[[v359]], %[[v357]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v360]], %[[v1672]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1665:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1667:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1665]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1668:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1667]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v363:[0-9]+]] = "llvm.load"(%[[v1668]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v364:[0-9]+]] = "llvm.shl"(%[[v363]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v365:[0-9]+]] = "llvm.lshr"(%[[v363]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v366:[0-9]+]] = "llvm.or"(%[[v364]], %[[v365]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1661:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1663:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1661]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1664:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1663]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v366]], %[[v1664]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1658:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v40]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1659:[0-9]+]] = "riscv.sextw"(%[[v1658]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1654:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1656:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1654]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1657:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1656]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v371:[0-9]+]] = "llvm.load"(%[[v1657]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1651:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v41]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1652:[0-9]+]] = "riscv.sextw"(%[[v1651]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1647:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1649:[0-9]+]] = "riscv.sh2add"(%[[v1652]], %[[v1647]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1650:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1649]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v374:[0-9]+]] = "llvm.load"(%[[v1650]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v375:[0-9]+]] = "llvm.add"(%[[v374]], %[[v371]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v375]], %[[v1650]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1643:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1645:[0-9]+]] = "riscv.sh2add"(%[[v1652]], %[[v1643]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1646:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1645]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v378:[0-9]+]] = "llvm.load"(%[[v1646]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1640:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v42]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1641:[0-9]+]] = "riscv.sextw"(%[[v1640]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1636:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1638:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1636]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1639:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1638]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v381:[0-9]+]] = "llvm.load"(%[[v1639]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v382:[0-9]+]] = "llvm.xor"(%[[v381]], %[[v378]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v382]], %[[v1639]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1632:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1634:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1632]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1635:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1634]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v385:[0-9]+]] = "llvm.load"(%[[v1635]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v386:[0-9]+]] = "llvm.shl"(%[[v385]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v387:[0-9]+]] = "llvm.lshr"(%[[v385]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v388:[0-9]+]] = "llvm.or"(%[[v386]], %[[v387]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1628:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1630:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1628]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1631:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1630]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v388]], %[[v1631]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1624:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1626:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1624]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1627:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1626]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v392:[0-9]+]] = "llvm.load"(%[[v1627]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1621:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v33]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1622:[0-9]+]] = "riscv.sextw"(%[[v1621]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1617:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1619:[0-9]+]] = "riscv.sh2add"(%[[v1622]], %[[v1617]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1620:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1619]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v395:[0-9]+]] = "llvm.load"(%[[v1620]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v396:[0-9]+]] = "llvm.add"(%[[v395]], %[[v392]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v396]], %[[v1620]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1613:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1615:[0-9]+]] = "riscv.sh2add"(%[[v1622]], %[[v1613]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1616:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1615]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v399:[0-9]+]] = "llvm.load"(%[[v1616]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1609:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1611:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1609]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1612:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1611]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v401:[0-9]+]] = "llvm.load"(%[[v1612]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v402:[0-9]+]] = "llvm.xor"(%[[v401]], %[[v399]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v402]], %[[v1612]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1605:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1607:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1605]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1608:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1607]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v405:[0-9]+]] = "llvm.load"(%[[v1608]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v406:[0-9]+]] = "llvm.shl"(%[[v405]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v407:[0-9]+]] = "llvm.lshr"(%[[v405]], %[[v244]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v408:[0-9]+]] = "llvm.or"(%[[v406]], %[[v407]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1601:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1603:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1601]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1604:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1603]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v408]], %[[v1604]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1597:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1599:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1597]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1600:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1599]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v412:[0-9]+]] = "llvm.load"(%[[v1600]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1593:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1595:[0-9]+]] = "riscv.sh2add"(%[[v1652]], %[[v1593]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1596:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1595]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v414:[0-9]+]] = "llvm.load"(%[[v1596]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v415:[0-9]+]] = "llvm.add"(%[[v414]], %[[v412]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v415]], %[[v1596]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1589:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1591:[0-9]+]] = "riscv.sh2add"(%[[v1652]], %[[v1589]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1592:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1591]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v418:[0-9]+]] = "llvm.load"(%[[v1592]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1585:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1587:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1585]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1588:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1587]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v420:[0-9]+]] = "llvm.load"(%[[v1588]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v421:[0-9]+]] = "llvm.xor"(%[[v420]], %[[v418]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v421]], %[[v1588]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1581:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1583:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1581]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1584:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1583]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v424:[0-9]+]] = "llvm.load"(%[[v1584]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v425:[0-9]+]] = "llvm.shl"(%[[v424]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v426:[0-9]+]] = "llvm.lshr"(%[[v424]], %[[v264]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v427:[0-9]+]] = "llvm.or"(%[[v425]], %[[v426]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1577:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1579:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1577]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1580:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1579]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v427]], %[[v1580]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1573:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1575:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1573]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1576:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1575]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v431:[0-9]+]] = "llvm.load"(%[[v1576]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1569:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1571:[0-9]+]] = "riscv.sh2add"(%[[v1622]], %[[v1569]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1572:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1571]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v433:[0-9]+]] = "llvm.load"(%[[v1572]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v434:[0-9]+]] = "llvm.add"(%[[v433]], %[[v431]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v434]], %[[v1572]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1565:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1567:[0-9]+]] = "riscv.sh2add"(%[[v1622]], %[[v1565]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1568:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1567]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v437:[0-9]+]] = "llvm.load"(%[[v1568]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1561:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1563:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1561]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1564:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1563]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v439:[0-9]+]] = "llvm.load"(%[[v1564]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v440:[0-9]+]] = "llvm.xor"(%[[v439]], %[[v437]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v440]], %[[v1564]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1557:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1559:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1557]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1560:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1559]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v443:[0-9]+]] = "llvm.load"(%[[v1560]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v444:[0-9]+]] = "llvm.shl"(%[[v443]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v445:[0-9]+]] = "llvm.lshr"(%[[v443]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v446:[0-9]+]] = "llvm.or"(%[[v444]], %[[v445]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1553:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1555:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1553]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1556:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1555]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v446]], %[[v1556]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1550:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v36]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1551:[0-9]+]] = "riscv.sextw"(%[[v1550]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1546:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1548:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1546]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1549:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1548]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v451:[0-9]+]] = "llvm.load"(%[[v1549]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1543:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v32]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1544:[0-9]+]] = "riscv.sextw"(%[[v1543]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1539:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1541:[0-9]+]] = "riscv.sh2add"(%[[v1544]], %[[v1539]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1542:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1541]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v454:[0-9]+]] = "llvm.load"(%[[v1542]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v455:[0-9]+]] = "llvm.add"(%[[v454]], %[[v451]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v455]], %[[v1542]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1535:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1537:[0-9]+]] = "riscv.sh2add"(%[[v1544]], %[[v1535]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1538:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1537]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v458:[0-9]+]] = "llvm.load"(%[[v1538]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1532:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v43]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1533:[0-9]+]] = "riscv.sextw"(%[[v1532]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1528:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1530:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1528]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1531:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1530]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v461:[0-9]+]] = "llvm.load"(%[[v1531]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v462:[0-9]+]] = "llvm.xor"(%[[v461]], %[[v458]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v462]], %[[v1531]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1524:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1526:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1524]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1527:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1526]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v465:[0-9]+]] = "llvm.load"(%[[v1527]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v466:[0-9]+]] = "llvm.shl"(%[[v465]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v467:[0-9]+]] = "llvm.lshr"(%[[v465]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v468:[0-9]+]] = "llvm.or"(%[[v466]], %[[v467]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1520:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1522:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1520]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1523:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1522]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v468]], %[[v1523]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1516:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1518:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1516]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1519:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1518]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v472:[0-9]+]] = "llvm.load"(%[[v1519]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1513:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v44]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1514:[0-9]+]] = "riscv.sextw"(%[[v1513]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1509:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1511:[0-9]+]] = "riscv.sh2add"(%[[v1514]], %[[v1509]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1512:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1511]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v475:[0-9]+]] = "llvm.load"(%[[v1512]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v476:[0-9]+]] = "llvm.add"(%[[v475]], %[[v472]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v476]], %[[v1512]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1505:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1507:[0-9]+]] = "riscv.sh2add"(%[[v1514]], %[[v1505]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1508:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1507]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v479:[0-9]+]] = "llvm.load"(%[[v1508]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1501:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1503:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1501]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1504:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1503]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v481:[0-9]+]] = "llvm.load"(%[[v1504]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v482:[0-9]+]] = "llvm.xor"(%[[v481]], %[[v479]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v482]], %[[v1504]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1497:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1499:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1497]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1500:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1499]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v485:[0-9]+]] = "llvm.load"(%[[v1500]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v486:[0-9]+]] = "llvm.shl"(%[[v485]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v487:[0-9]+]] = "llvm.lshr"(%[[v485]], %[[v244]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v488:[0-9]+]] = "llvm.or"(%[[v486]], %[[v487]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1493:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1495:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1493]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1496:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1495]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v488]], %[[v1496]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1489:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1491:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1489]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1492:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1491]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v492:[0-9]+]] = "llvm.load"(%[[v1492]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1485:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1487:[0-9]+]] = "riscv.sh2add"(%[[v1544]], %[[v1485]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1488:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1487]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v494:[0-9]+]] = "llvm.load"(%[[v1488]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v495:[0-9]+]] = "llvm.add"(%[[v494]], %[[v492]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v495]], %[[v1488]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1481:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1483:[0-9]+]] = "riscv.sh2add"(%[[v1544]], %[[v1481]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1484:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1483]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v498:[0-9]+]] = "llvm.load"(%[[v1484]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1477:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1479:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1477]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1480:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1479]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v500:[0-9]+]] = "llvm.load"(%[[v1480]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v501:[0-9]+]] = "llvm.xor"(%[[v500]], %[[v498]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v501]], %[[v1480]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1473:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1475:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1473]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1476:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1475]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v504:[0-9]+]] = "llvm.load"(%[[v1476]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v505:[0-9]+]] = "llvm.shl"(%[[v504]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v506:[0-9]+]] = "llvm.lshr"(%[[v504]], %[[v264]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v507:[0-9]+]] = "llvm.or"(%[[v505]], %[[v506]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1469:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1471:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1469]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1472:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1471]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v507]], %[[v1472]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1465:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1467:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1465]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1468:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1467]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v511:[0-9]+]] = "llvm.load"(%[[v1468]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1461:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1463:[0-9]+]] = "riscv.sh2add"(%[[v1514]], %[[v1461]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1464:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1463]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v513:[0-9]+]] = "llvm.load"(%[[v1464]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v514:[0-9]+]] = "llvm.add"(%[[v513]], %[[v511]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v514]], %[[v1464]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1457:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1459:[0-9]+]] = "riscv.sh2add"(%[[v1514]], %[[v1457]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1460:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1459]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v517:[0-9]+]] = "llvm.load"(%[[v1460]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1453:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1455:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1453]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1456:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1455]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v519:[0-9]+]] = "llvm.load"(%[[v1456]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v520:[0-9]+]] = "llvm.xor"(%[[v519]], %[[v517]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v520]], %[[v1456]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1449:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1451:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1449]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1452:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1451]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v523:[0-9]+]] = "llvm.load"(%[[v1452]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v524:[0-9]+]] = "llvm.shl"(%[[v523]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v525:[0-9]+]] = "llvm.lshr"(%[[v523]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v526:[0-9]+]] = "llvm.or"(%[[v524]], %[[v525]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1445:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1447:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1445]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1448:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1447]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v526]], %[[v1448]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1441:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1443:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1441]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1444:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1443]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v530:[0-9]+]] = "llvm.load"(%[[v1444]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1437:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1439:[0-9]+]] = "riscv.sh2add"(%[[v1868]], %[[v1437]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1440:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1439]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v532:[0-9]+]] = "llvm.load"(%[[v1440]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v533:[0-9]+]] = "llvm.add"(%[[v532]], %[[v530]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v533]], %[[v1440]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1433:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1435:[0-9]+]] = "riscv.sh2add"(%[[v1868]], %[[v1433]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1436:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1435]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v536:[0-9]+]] = "llvm.load"(%[[v1436]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1429:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1431:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1429]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1432:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1431]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v538:[0-9]+]] = "llvm.load"(%[[v1432]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v539:[0-9]+]] = "llvm.xor"(%[[v538]], %[[v536]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v539]], %[[v1432]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1425:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1427:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1425]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1428:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1427]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v542:[0-9]+]] = "llvm.load"(%[[v1428]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v543:[0-9]+]] = "llvm.shl"(%[[v542]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v544:[0-9]+]] = "llvm.lshr"(%[[v542]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v545:[0-9]+]] = "llvm.or"(%[[v543]], %[[v544]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1421:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1423:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1421]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1424:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1423]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v545]], %[[v1424]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1417:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1419:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1417]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1420:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1419]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v549:[0-9]+]] = "llvm.load"(%[[v1420]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1413:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1415:[0-9]+]] = "riscv.sh2add"(%[[v1622]], %[[v1413]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1416:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1415]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v551:[0-9]+]] = "llvm.load"(%[[v1416]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v552:[0-9]+]] = "llvm.add"(%[[v551]], %[[v549]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v552]], %[[v1416]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1409:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1411:[0-9]+]] = "riscv.sh2add"(%[[v1622]], %[[v1409]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1412:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1411]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v555:[0-9]+]] = "llvm.load"(%[[v1412]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1405:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1407:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1405]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1408:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1407]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v557:[0-9]+]] = "llvm.load"(%[[v1408]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v558:[0-9]+]] = "llvm.xor"(%[[v557]], %[[v555]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v558]], %[[v1408]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1401:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1403:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1401]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1404:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1403]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v561:[0-9]+]] = "llvm.load"(%[[v1404]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v562:[0-9]+]] = "llvm.shl"(%[[v561]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v563:[0-9]+]] = "llvm.lshr"(%[[v561]], %[[v244]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v564:[0-9]+]] = "llvm.or"(%[[v562]], %[[v563]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1397:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1399:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1397]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1400:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1399]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v564]], %[[v1400]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1393:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1395:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1393]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1396:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1395]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v568:[0-9]+]] = "llvm.load"(%[[v1396]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1389:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1391:[0-9]+]] = "riscv.sh2add"(%[[v1868]], %[[v1389]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1392:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1391]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v570:[0-9]+]] = "llvm.load"(%[[v1392]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v571:[0-9]+]] = "llvm.add"(%[[v570]], %[[v568]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v571]], %[[v1392]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1385:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1387:[0-9]+]] = "riscv.sh2add"(%[[v1868]], %[[v1385]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1388:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1387]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v574:[0-9]+]] = "llvm.load"(%[[v1388]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1381:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1383:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1381]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1384:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1383]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v576:[0-9]+]] = "llvm.load"(%[[v1384]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v577:[0-9]+]] = "llvm.xor"(%[[v576]], %[[v574]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v577]], %[[v1384]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1377:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1379:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1377]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1380:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1379]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v580:[0-9]+]] = "llvm.load"(%[[v1380]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v581:[0-9]+]] = "llvm.shl"(%[[v580]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v582:[0-9]+]] = "llvm.lshr"(%[[v580]], %[[v264]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v583:[0-9]+]] = "llvm.or"(%[[v581]], %[[v582]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1373:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1375:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1373]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1376:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1375]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v583]], %[[v1376]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1369:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1371:[0-9]+]] = "riscv.sh2add"(%[[v1533]], %[[v1369]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1372:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1371]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v587:[0-9]+]] = "llvm.load"(%[[v1372]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1365:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1367:[0-9]+]] = "riscv.sh2add"(%[[v1622]], %[[v1365]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1368:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1367]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v589:[0-9]+]] = "llvm.load"(%[[v1368]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v590:[0-9]+]] = "llvm.add"(%[[v589]], %[[v587]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v590]], %[[v1368]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1361:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1363:[0-9]+]] = "riscv.sh2add"(%[[v1622]], %[[v1361]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1364:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1363]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v593:[0-9]+]] = "llvm.load"(%[[v1364]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1357:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1359:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1357]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1360:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1359]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v595:[0-9]+]] = "llvm.load"(%[[v1360]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v596:[0-9]+]] = "llvm.xor"(%[[v595]], %[[v593]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v596]], %[[v1360]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1353:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1355:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1353]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1356:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1355]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v599:[0-9]+]] = "llvm.load"(%[[v1356]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v600:[0-9]+]] = "llvm.shl"(%[[v599]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v601:[0-9]+]] = "llvm.lshr"(%[[v599]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v602:[0-9]+]] = "llvm.or"(%[[v600]], %[[v601]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1349:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1351:[0-9]+]] = "riscv.sh2add"(%[[v1767]], %[[v1349]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1352:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1351]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v602]], %[[v1352]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1345:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1347:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1345]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1348:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1347]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v606:[0-9]+]] = "llvm.load"(%[[v1348]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1341:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1343:[0-9]+]] = "riscv.sh2add"(%[[v1760]], %[[v1341]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1344:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1343]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v608:[0-9]+]] = "llvm.load"(%[[v1344]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v609:[0-9]+]] = "llvm.add"(%[[v608]], %[[v606]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v609]], %[[v1344]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1337:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1339:[0-9]+]] = "riscv.sh2add"(%[[v1760]], %[[v1337]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1340:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1339]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v612:[0-9]+]] = "llvm.load"(%[[v1340]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1333:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1335:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1333]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1336:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1335]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v614:[0-9]+]] = "llvm.load"(%[[v1336]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v615:[0-9]+]] = "llvm.xor"(%[[v614]], %[[v612]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v615]], %[[v1336]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1329:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1331:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1329]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1332:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1331]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v618:[0-9]+]] = "llvm.load"(%[[v1332]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v619:[0-9]+]] = "llvm.shl"(%[[v618]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v620:[0-9]+]] = "llvm.lshr"(%[[v618]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v621:[0-9]+]] = "llvm.or"(%[[v619]], %[[v620]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1325:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1327:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1325]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1328:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1327]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v621]], %[[v1328]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1321:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1323:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1321]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1324:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1323]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v625:[0-9]+]] = "llvm.load"(%[[v1324]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1317:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1319:[0-9]+]] = "riscv.sh2add"(%[[v1514]], %[[v1317]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1320:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1319]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v627:[0-9]+]] = "llvm.load"(%[[v1320]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v628:[0-9]+]] = "llvm.add"(%[[v627]], %[[v625]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v628]], %[[v1320]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1313:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1315:[0-9]+]] = "riscv.sh2add"(%[[v1514]], %[[v1313]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1316:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1315]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v631:[0-9]+]] = "llvm.load"(%[[v1316]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1309:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1311:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1309]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1312:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1311]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v633:[0-9]+]] = "llvm.load"(%[[v1312]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v634:[0-9]+]] = "llvm.xor"(%[[v633]], %[[v631]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v634]], %[[v1312]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1305:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1307:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1305]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1308:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1307]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v637:[0-9]+]] = "llvm.load"(%[[v1308]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v638:[0-9]+]] = "llvm.shl"(%[[v637]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v639:[0-9]+]] = "llvm.lshr"(%[[v637]], %[[v244]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v640:[0-9]+]] = "llvm.or"(%[[v638]], %[[v639]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1301:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1303:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1301]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1304:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1303]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v640]], %[[v1304]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1297:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1299:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1297]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1300:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1299]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v644:[0-9]+]] = "llvm.load"(%[[v1300]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1293:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1295:[0-9]+]] = "riscv.sh2add"(%[[v1760]], %[[v1293]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1296:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1295]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v646:[0-9]+]] = "llvm.load"(%[[v1296]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v647:[0-9]+]] = "llvm.add"(%[[v646]], %[[v644]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v647]], %[[v1296]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1289:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1291:[0-9]+]] = "riscv.sh2add"(%[[v1760]], %[[v1289]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1292:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1291]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v650:[0-9]+]] = "llvm.load"(%[[v1292]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1285:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1287:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1285]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1288:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1287]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v652:[0-9]+]] = "llvm.load"(%[[v1288]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v653:[0-9]+]] = "llvm.xor"(%[[v652]], %[[v650]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v653]], %[[v1288]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1281:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1283:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1281]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1284:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1283]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v656:[0-9]+]] = "llvm.load"(%[[v1284]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v657:[0-9]+]] = "llvm.shl"(%[[v656]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v658:[0-9]+]] = "llvm.lshr"(%[[v656]], %[[v264]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v659:[0-9]+]] = "llvm.or"(%[[v657]], %[[v658]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1277:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1279:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1277]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1280:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1279]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v659]], %[[v1280]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1273:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1275:[0-9]+]] = "riscv.sh2add"(%[[v1857]], %[[v1273]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1276:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1275]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v663:[0-9]+]] = "llvm.load"(%[[v1276]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1269:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1271:[0-9]+]] = "riscv.sh2add"(%[[v1514]], %[[v1269]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1272:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1271]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v665:[0-9]+]] = "llvm.load"(%[[v1272]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v666:[0-9]+]] = "llvm.add"(%[[v665]], %[[v663]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v666]], %[[v1272]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1265:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1267:[0-9]+]] = "riscv.sh2add"(%[[v1514]], %[[v1265]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1268:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1267]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v669:[0-9]+]] = "llvm.load"(%[[v1268]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1261:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1263:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1261]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1264:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1263]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v671:[0-9]+]] = "llvm.load"(%[[v1264]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v672:[0-9]+]] = "llvm.xor"(%[[v671]], %[[v669]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v672]], %[[v1264]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1257:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1259:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1257]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1260:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1259]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v675:[0-9]+]] = "llvm.load"(%[[v1260]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v676:[0-9]+]] = "llvm.shl"(%[[v675]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v677:[0-9]+]] = "llvm.lshr"(%[[v675]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v678:[0-9]+]] = "llvm.or"(%[[v676]], %[[v677]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1253:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1255:[0-9]+]] = "riscv.sh2add"(%[[v1659]], %[[v1253]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1256:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1255]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v678]], %[[v1256]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1249:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1251:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1249]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1252:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1251]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v682:[0-9]+]] = "llvm.load"(%[[v1252]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1245:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1247:[0-9]+]] = "riscv.sh2add"(%[[v1652]], %[[v1245]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1248:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1247]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v684:[0-9]+]] = "llvm.load"(%[[v1248]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v685:[0-9]+]] = "llvm.add"(%[[v684]], %[[v682]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v685]], %[[v1248]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1241:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1243:[0-9]+]] = "riscv.sh2add"(%[[v1652]], %[[v1241]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1244:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1243]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v688:[0-9]+]] = "llvm.load"(%[[v1244]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1237:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1239:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1237]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1240:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1239]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v690:[0-9]+]] = "llvm.load"(%[[v1240]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v691:[0-9]+]] = "llvm.xor"(%[[v690]], %[[v688]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v691]], %[[v1240]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1233:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1235:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1233]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1236:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1235]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v694:[0-9]+]] = "llvm.load"(%[[v1236]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v695:[0-9]+]] = "llvm.shl"(%[[v694]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v696:[0-9]+]] = "llvm.lshr"(%[[v694]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v697:[0-9]+]] = "llvm.or"(%[[v695]], %[[v696]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1229:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1231:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1229]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1232:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1231]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v697]], %[[v1232]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1225:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1227:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1225]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1228:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1227]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v701:[0-9]+]] = "llvm.load"(%[[v1228]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1221:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1223:[0-9]+]] = "riscv.sh2add"(%[[v1838]], %[[v1221]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1224:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1223]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v703:[0-9]+]] = "llvm.load"(%[[v1224]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v704:[0-9]+]] = "llvm.add"(%[[v703]], %[[v701]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v704]], %[[v1224]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1217:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1219:[0-9]+]] = "riscv.sh2add"(%[[v1838]], %[[v1217]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1220:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1219]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v707:[0-9]+]] = "llvm.load"(%[[v1220]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1213:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1215:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1213]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1216:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1215]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v709:[0-9]+]] = "llvm.load"(%[[v1216]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v710:[0-9]+]] = "llvm.xor"(%[[v709]], %[[v707]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v710]], %[[v1216]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1209:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1211:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1209]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1212:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1211]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v713:[0-9]+]] = "llvm.load"(%[[v1212]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v714:[0-9]+]] = "llvm.shl"(%[[v713]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v715:[0-9]+]] = "llvm.lshr"(%[[v713]], %[[v244]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v716:[0-9]+]] = "llvm.or"(%[[v714]], %[[v715]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1205:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1207:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1205]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1208:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1207]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v716]], %[[v1208]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1201:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1203:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1201]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1204:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1203]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v720:[0-9]+]] = "llvm.load"(%[[v1204]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1197:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1199:[0-9]+]] = "riscv.sh2add"(%[[v1652]], %[[v1197]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1200:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1199]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v722:[0-9]+]] = "llvm.load"(%[[v1200]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v723:[0-9]+]] = "llvm.add"(%[[v722]], %[[v720]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v723]], %[[v1200]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1193:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1195:[0-9]+]] = "riscv.sh2add"(%[[v1652]], %[[v1193]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1196:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1195]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v726:[0-9]+]] = "llvm.load"(%[[v1196]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1189:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1191:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1189]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1192:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1191]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v728:[0-9]+]] = "llvm.load"(%[[v1192]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v729:[0-9]+]] = "llvm.xor"(%[[v728]], %[[v726]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v729]], %[[v1192]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1185:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1187:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1185]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1188:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1187]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v732:[0-9]+]] = "llvm.load"(%[[v1188]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v733:[0-9]+]] = "llvm.shl"(%[[v732]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v734:[0-9]+]] = "llvm.lshr"(%[[v732]], %[[v264]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v735:[0-9]+]] = "llvm.or"(%[[v733]], %[[v734]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1181:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1183:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1181]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1184:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1183]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v735]], %[[v1184]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1177:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1179:[0-9]+]] = "riscv.sh2add"(%[[v1749]], %[[v1177]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1180:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1179]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v739:[0-9]+]] = "llvm.load"(%[[v1180]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1173:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1175:[0-9]+]] = "riscv.sh2add"(%[[v1838]], %[[v1173]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1176:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1175]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v741:[0-9]+]] = "llvm.load"(%[[v1176]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v742:[0-9]+]] = "llvm.add"(%[[v741]], %[[v739]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v742]], %[[v1176]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1169:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1171:[0-9]+]] = "riscv.sh2add"(%[[v1838]], %[[v1169]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1172:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1171]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v745:[0-9]+]] = "llvm.load"(%[[v1172]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1165:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1167:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1165]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1168:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1167]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v747:[0-9]+]] = "llvm.load"(%[[v1168]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v748:[0-9]+]] = "llvm.xor"(%[[v747]], %[[v745]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v748]], %[[v1168]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1161:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1163:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1161]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1164:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1163]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v751:[0-9]+]] = "llvm.load"(%[[v1164]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v752:[0-9]+]] = "llvm.shl"(%[[v751]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v753:[0-9]+]] = "llvm.lshr"(%[[v751]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v754:[0-9]+]] = "llvm.or"(%[[v752]], %[[v753]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1157:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1159:[0-9]+]] = "riscv.sh2add"(%[[v1551]], %[[v1157]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1160:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1159]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v754]], %[[v1160]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1153:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1155:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1153]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1156:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1155]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v758:[0-9]+]] = "llvm.load"(%[[v1156]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1149:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1151:[0-9]+]] = "riscv.sh2add"(%[[v1544]], %[[v1149]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1152:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1151]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v760:[0-9]+]] = "llvm.load"(%[[v1152]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v761:[0-9]+]] = "llvm.add"(%[[v760]], %[[v758]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v761]], %[[v1152]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1145:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1147:[0-9]+]] = "riscv.sh2add"(%[[v1544]], %[[v1145]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1148:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1147]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v764:[0-9]+]] = "llvm.load"(%[[v1148]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1141:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1143:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1141]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1144:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1143]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v766:[0-9]+]] = "llvm.load"(%[[v1144]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v767:[0-9]+]] = "llvm.xor"(%[[v766]], %[[v764]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v767]], %[[v1144]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1137:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1139:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1137]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1140:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1139]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v770:[0-9]+]] = "llvm.load"(%[[v1140]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v771:[0-9]+]] = "llvm.shl"(%[[v770]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v772:[0-9]+]] = "llvm.lshr"(%[[v770]], %[[v223]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v773:[0-9]+]] = "llvm.or"(%[[v771]], %[[v772]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1133:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1135:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1133]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1136:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1135]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v773]], %[[v1136]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1129:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1131:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1129]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1132:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1131]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v777:[0-9]+]] = "llvm.load"(%[[v1132]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1125:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1127:[0-9]+]] = "riscv.sh2add"(%[[v1730]], %[[v1125]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1128:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1127]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v779:[0-9]+]] = "llvm.load"(%[[v1128]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v780:[0-9]+]] = "llvm.add"(%[[v779]], %[[v777]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v780]], %[[v1128]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1121:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1123:[0-9]+]] = "riscv.sh2add"(%[[v1730]], %[[v1121]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1124:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1123]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v783:[0-9]+]] = "llvm.load"(%[[v1124]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1117:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1119:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1117]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1120:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1119]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v785:[0-9]+]] = "llvm.load"(%[[v1120]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v786:[0-9]+]] = "llvm.xor"(%[[v785]], %[[v783]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v786]], %[[v1120]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1113:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1115:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1113]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1116:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1115]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v789:[0-9]+]] = "llvm.load"(%[[v1116]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v790:[0-9]+]] = "llvm.shl"(%[[v789]], %[[v11]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v791:[0-9]+]] = "llvm.lshr"(%[[v789]], %[[v244]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v792:[0-9]+]] = "llvm.or"(%[[v790]], %[[v791]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1109:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1111:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1109]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1112:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1111]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v792]], %[[v1112]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1105:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1107:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1105]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1108:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1107]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v796:[0-9]+]] = "llvm.load"(%[[v1108]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1101:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1103:[0-9]+]] = "riscv.sh2add"(%[[v1544]], %[[v1101]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1104:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1103]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v798:[0-9]+]] = "llvm.load"(%[[v1104]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v799:[0-9]+]] = "llvm.add"(%[[v798]], %[[v796]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v799]], %[[v1104]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1097:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1099:[0-9]+]] = "riscv.sh2add"(%[[v1544]], %[[v1097]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1100:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1099]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v802:[0-9]+]] = "llvm.load"(%[[v1100]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1093:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1095:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1093]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1096:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1095]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v804:[0-9]+]] = "llvm.load"(%[[v1096]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v805:[0-9]+]] = "llvm.xor"(%[[v804]], %[[v802]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v805]], %[[v1096]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1089:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1091:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1089]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1092:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1091]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v808:[0-9]+]] = "llvm.load"(%[[v1092]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v809:[0-9]+]] = "llvm.shl"(%[[v808]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v810:[0-9]+]] = "llvm.lshr"(%[[v808]], %[[v264]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v811:[0-9]+]] = "llvm.or"(%[[v809]], %[[v810]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1085:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1087:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1085]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1088:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1087]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v811]], %[[v1088]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1081:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1083:[0-9]+]] = "riscv.sh2add"(%[[v1641]], %[[v1081]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1084:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1083]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v815:[0-9]+]] = "llvm.load"(%[[v1084]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1077:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1079:[0-9]+]] = "riscv.sh2add"(%[[v1730]], %[[v1077]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1080:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1079]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v817:[0-9]+]] = "llvm.load"(%[[v1080]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v818:[0-9]+]] = "llvm.add"(%[[v817]], %[[v815]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v818]], %[[v1080]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1073:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1075:[0-9]+]] = "riscv.sh2add"(%[[v1730]], %[[v1073]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1076:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1075]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v821:[0-9]+]] = "llvm.load"(%[[v1076]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v1069:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1071:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1069]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1072:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1071]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v823:[0-9]+]] = "llvm.load"(%[[v1072]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v824:[0-9]+]] = "llvm.xor"(%[[v823]], %[[v821]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v824]], %[[v1072]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1065:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1067:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1065]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1068:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1067]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v827:[0-9]+]] = "llvm.load"(%[[v1068]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v828:[0-9]+]] = "llvm.shl"(%[[v827]], %[[v36]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v829:[0-9]+]] = "llvm.lshr"(%[[v827]], %[[v284]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v830:[0-9]+]] = "llvm.or"(%[[v828]], %[[v829]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1061:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v47]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1063:[0-9]+]] = "riscv.sh2add"(%[[v1875]], %[[v1061]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1064:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1063]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v830]], %[[v1064]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v833:[0-9]+]] = "llvm.add"(%[[v933]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v929:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v833]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v929]]) [^[[bb199]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb203]]():
// CHECK-NEXT:         %[[v917:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v9]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v917]]) [^[[bb835:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb835]](%[[varg835_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v919:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg835_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v837:[0-9]+]] = "llvm.icmp"(%[[v919]], %[[v25]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         %[[v925:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v837]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v925]]) [^[[bb838:[0-9]+]], ^[[bb839:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb838]]():
// CHECK-NEXT:         %[[v841:[0-9]+]] = "llvm.mul"(%[[v35]], %[[v919]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1058:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v841]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1059:[0-9]+]] = "riscv.sextw"(%[[v1058]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1054:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v48]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1056:[0-9]+]] = "riscv.add"(%[[v1054]], %[[v1059]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1057:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1056]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v1051:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v919]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1052:[0-9]+]] = "riscv.sextw"(%[[v1051]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1053:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1052]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v845:[0-9]+]] = "llvm.getelementptr"(%[[v47]], %[[v1954]], %[[v1053]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v846:[0-9]+]] = "llvm.load"(%[[v845]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v847:[0-9]+]] = "llvm.getelementptr"(%[[v46]], %[[v1954]], %[[v1053]]) <{"elem_type" = !llvm.array<16 x i32>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v848:[0-9]+]] = "llvm.load"(%[[v847]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v849:[0-9]+]] = "llvm.add"(%[[v846]], %[[v848]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1049:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v849]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1050:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1049]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         "llvm.store"(%[[v1050]], %[[v1057]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v852:[0-9]+]] = "llvm.lshr"(%[[v849]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1047:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v852]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1048:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1047]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v1043:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1057]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1045:[0-9]+]] = "riscv.add"(%[[v1043]], %[[v1949]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1046:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1045]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1048]], %[[v1046]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v856:[0-9]+]] = "llvm.lshr"(%[[v849]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1041:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v856]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1042:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1041]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v1037:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1057]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1039:[0-9]+]] = "riscv.add"(%[[v1037]], %[[v1947]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1040:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1039]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1042]], %[[v1040]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v860:[0-9]+]] = "llvm.lshr"(%[[v849]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1035:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v860]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1036:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1035]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v1031:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1057]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1033:[0-9]+]] = "riscv.add"(%[[v1031]], %[[v1945]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1034:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1033]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1036]], %[[v1034]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v864:[0-9]+]] = "llvm.add"(%[[v919]], %[[v8]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v915:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v864]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v915]]) [^[[bb835]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb839]]():
// CHECK-NEXT:         %[[v866:[0-9]+]] = "llvm.add"(%[[v969]], %[[v8]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1029:[0-9]+]] = "riscv.sub"(%[[v1943]], %[[varg107_1]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1025:[0-9]+]] = "riscv.sltu"(%[[v1939]], %[[v1029]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1026:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1025]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v952:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1026]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v952]], %[[v1029]]) [^[[bb869:[0-9]+]], ^[[bb870:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb869]]():
// CHECK-NEXT:         "riscv_cf.branch"(%[[v1939]]) [^[[bb870]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb870]](%[[varg870_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.branch"(%[[v1953]]) [^[[bb873:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb873]](%[[varg873_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v962:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg873_0]]) : (!riscv.reg) -> i64
// CHECK-NEXT:         %[[v1021:[0-9]+]] = "riscv.sltu"(%[[varg873_0]], %[[varg870_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1022:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1021]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v971:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1022]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v971]]) [^[[bb876:[0-9]+]], ^[[bb877:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb876]]():
// CHECK-NEXT:         %[[v1017:[0-9]+]] = "riscv.add"(%[[varg873_0]], %[[varg107_1]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1011:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v105]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1013:[0-9]+]] = "riscv.add"(%[[v1011]], %[[v1017]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1014:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1013]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         %[[v881:[0-9]+]] = "llvm.load"(%[[v1014]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v882:[0-9]+]] = "llvm.zext"(%[[v881]]) : (i8) -> i32
// CHECK-NEXT:         %[[v883:[0-9]+]] = "llvm.getelementptr"(%[[v48]], %[[v1954]], %[[v962]]) <{"elem_type" = !llvm.array<64 x i8>, "noWrapFlags" = 7 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v884:[0-9]+]] = "llvm.load"(%[[v883]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v885:[0-9]+]] = "llvm.zext"(%[[v884]]) : (i8) -> i32
// CHECK-NEXT:         %[[v886:[0-9]+]] = "llvm.xor"(%[[v882]], %[[v885]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v1009:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v886]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1010:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1009]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v1005:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v106]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v1007:[0-9]+]] = "riscv.add"(%[[v1005]], %[[v1017]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1008:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1007]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v1010]], %[[v1008]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v1003:[0-9]+]] = "riscv.add"(%[[v1949]], %[[varg873_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v1003]]) [^[[bb873]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb877]]():
// CHECK-NEXT:         %[[v999:[0-9]+]] = "riscv.add"(%[[varg870_0]], %[[varg107_1]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v963:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v866]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v963]], %[[v999]]) [^[[bb107]]] : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb111]]():
// CHECK-NEXT:         %[[v894:[0-9]+]] = "llvm.getelementptr"(%[[v52]], %[[v1954]], %[[v1954]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v895:[0-9]+]] = "llvm.load"(%[[v894]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v896:[0-9]+]] = "llvm.zext"(%[[v895]]) : (i8) -> i32
// CHECK-NEXT:         %[[v897:[0-9]+]] = "llvm.shl"(%[[v896]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v898:[0-9]+]] = "llvm.getelementptr"(%[[v52]], %[[v1954]], %[[v1950]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v899:[0-9]+]] = "llvm.load"(%[[v898]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v900:[0-9]+]] = "llvm.zext"(%[[v899]]) : (i8) -> i32
// CHECK-NEXT:         %[[v901:[0-9]+]] = "llvm.shl"(%[[v900]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v902:[0-9]+]] = "llvm.or"(%[[v897]], %[[v901]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v903:[0-9]+]] = "llvm.getelementptr"(%[[v52]], %[[v1954]], %[[v1948]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v904:[0-9]+]] = "llvm.load"(%[[v903]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v905:[0-9]+]] = "llvm.zext"(%[[v904]]) : (i8) -> i32
// CHECK-NEXT:         %[[v906:[0-9]+]] = "llvm.shl"(%[[v905]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v907:[0-9]+]] = "llvm.or"(%[[v902]], %[[v906]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v908:[0-9]+]] = "llvm.getelementptr"(%[[v52]], %[[v1954]], %[[v1946]]) <{"elem_type" = !llvm.array<114 x i8>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v909:[0-9]+]] = "llvm.load"(%[[v908]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v910:[0-9]+]] = "llvm.zext"(%[[v909]]) : (i8) -> i32
// CHECK-NEXT:         %[[v911:[0-9]+]] = "llvm.or"(%[[v907]], %[[v910]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.return"(%[[v911]]) : (i32) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()

