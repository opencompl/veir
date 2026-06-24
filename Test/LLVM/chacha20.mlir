// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 1 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 4 : i32>]}> : () -> ()
    "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, always_inline, "arg_attrs" = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], "frame_pointer" = #llvm.framePointerKind<"non-leaf-no-reserve">, "function_type" = !llvm.func<void (!llvm.ptr, i32, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr)>, "linkage" = #llvm.linkage<external>, no_unwind, "passthrough" = ["ssp", ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "apple-m1"]], "sym_name" = "chacha20_block", "target_cpu" = "apple-m1", "target_features" = #llvm.target_features<["+aes", "+altnzcv", "+ccdp", "+ccidx", "+ccpp", "+complxnum", "+crc", "+dit", "+dotprod", "+flagm", "+fp-armv8", "+fp16fml", "+fptoint", "+fullfp16", "+jsconv", "+lse", "+neon", "+pauth", "+perfmon", "+predres", "+ras", "+rcpc", "+rdm", "+sb", "+sha2", "+sha3", "+specrestrict", "+ssbs", "+v8.1a", "+v8.2a", "+v8.3a", "+v8.4a", "+v8a"]>, "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<sync>, "visibility_" = 0 : i64}> ({
      ^7(%arg7_0 : !llvm.ptr, %arg7_1 : i32, %arg7_2 : !llvm.ptr, %arg7_3 : !llvm.ptr, %arg7_4 : !llvm.ptr, %arg7_5 : !llvm.ptr):
        %8 = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
        %9 = "llvm.mlir.constant"() <{"value" = 1634760805 : i32}> : () -> i32
        %10 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
        %11 = "llvm.mlir.constant"() <{"value" = 857760878 : i32}> : () -> i32
        %12 = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
        %13 = "llvm.mlir.constant"() <{"value" = 2036477234 : i32}> : () -> i32
        %14 = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
        %15 = "llvm.mlir.constant"() <{"value" = 1797285236 : i32}> : () -> i32
        %16 = "llvm.mlir.constant"() <{"value" = 8 : i64}> : () -> i64
        %17 = "llvm.mlir.constant"() <{"value" = 12 : i64}> : () -> i64
        %18 = "llvm.mlir.constant"() <{"value" = 16 : i64}> : () -> i64
        %19 = "llvm.mlir.constant"() <{"value" = 10 : i64}> : () -> i64
        %20 = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
        %21 = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
        %22 = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
        %23 = "llvm.mlir.constant"() <{"value" = 24 : i32}> : () -> i32
        %24 = "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
        %25 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
        %26 = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
        %27 = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
        %28 = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
        %29 = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
        %30 = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
        %31 = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
        %32 = "llvm.mlir.constant"() <{"value" = 9 : i32}> : () -> i32
        %33 = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
        %34 = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
        %35 = "llvm.mlir.constant"() <{"value" = 14 : i32}> : () -> i32
        %36 = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
        %37 = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
        %38 = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
        %39 = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
        %40 = "llvm.mlir.constant"() <{"value" = 13 : i64}> : () -> i64
        %41 = "llvm.getelementptr"(%arg7_4, %8) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%9, %41) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %43 = "llvm.getelementptr"(%arg7_4, %10) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%11, %43) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %45 = "llvm.getelementptr"(%arg7_4, %12) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%13, %45) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %47 = "llvm.getelementptr"(%arg7_4, %14) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%15, %47) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"(%8) [^49] : (i64) -> ()
      ^49(%arg49_0 : i64):
        %51 = "llvm.icmp"(%arg49_0, %16) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%51) [^52, ^53] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^52():
        %55 = "llvm.mul"(%20, %arg49_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %56 = "llvm.getelementptr"(%arg7_0, %55) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %57 = "llvm.load"(%56) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %58 = "llvm.zext"(%57) : (i8) -> i32
        %59 = "llvm.getelementptr"(%56, %10) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %60 = "llvm.load"(%59) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %61 = "llvm.zext"(%60) : (i8) -> i32
        %62 = "llvm.shl"(%61, %21) : (i32, i32) -> i32
        %63 = "llvm.or"(%58, %62) : (i32, i32) -> i32
        %64 = "llvm.getelementptr"(%56, %12) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %65 = "llvm.load"(%64) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %66 = "llvm.zext"(%65) : (i8) -> i32
        %67 = "llvm.shl"(%66, %22) : (i32, i32) -> i32
        %68 = "llvm.or"(%63, %67) : (i32, i32) -> i32
        %69 = "llvm.getelementptr"(%56, %14) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %70 = "llvm.load"(%69) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %71 = "llvm.zext"(%70) : (i8) -> i32
        %72 = "llvm.shl"(%71, %23) : (i32, i32) -> i32
        %73 = "llvm.or"(%68, %72) : (i32, i32) -> i32
        %74 = "llvm.add"(%20, %arg49_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %75 = "llvm.getelementptr"(%arg7_4, %74) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%73, %75) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"() [^77] : () -> ()
      ^77():
        %79 = "llvm.add"(%arg49_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%79) [^49] : (i64) -> ()
      ^53():
        %81 = "llvm.getelementptr"(%arg7_4, %17) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%arg7_1, %81) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"(%8) [^83] : (i64) -> ()
      ^83(%arg83_0 : i64):
        %85 = "llvm.icmp"(%arg83_0, %14) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%85) [^86, ^87] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^86():
        %89 = "llvm.mul"(%20, %arg83_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %90 = "llvm.getelementptr"(%arg7_2, %89) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %91 = "llvm.load"(%90) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %92 = "llvm.zext"(%91) : (i8) -> i32
        %93 = "llvm.getelementptr"(%90, %10) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %94 = "llvm.load"(%93) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %95 = "llvm.zext"(%94) : (i8) -> i32
        %96 = "llvm.shl"(%95, %21) : (i32, i32) -> i32
        %97 = "llvm.or"(%92, %96) : (i32, i32) -> i32
        %98 = "llvm.getelementptr"(%90, %12) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %99 = "llvm.load"(%98) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %100 = "llvm.zext"(%99) : (i8) -> i32
        %101 = "llvm.shl"(%100, %22) : (i32, i32) -> i32
        %102 = "llvm.or"(%97, %101) : (i32, i32) -> i32
        %103 = "llvm.getelementptr"(%90, %14) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %104 = "llvm.load"(%103) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
        %105 = "llvm.zext"(%104) : (i8) -> i32
        %106 = "llvm.shl"(%105, %23) : (i32, i32) -> i32
        %107 = "llvm.or"(%102, %106) : (i32, i32) -> i32
        %108 = "llvm.add"(%40, %arg83_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %109 = "llvm.getelementptr"(%arg7_4, %108) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%107, %109) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"() [^111] : () -> ()
      ^111():
        %113 = "llvm.add"(%arg83_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%113) [^83] : (i64) -> ()
      ^87():
        "llvm.br"(%8) [^115] : (i64) -> ()
      ^115(%arg115_0 : i64):
        %117 = "llvm.icmp"(%arg115_0, %18) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%117) [^118, ^119] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^118():
        %121 = "llvm.getelementptr"(%arg7_4, %arg115_0) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %122 = "llvm.load"(%121) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %123 = "llvm.getelementptr"(%arg7_5, %arg115_0) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%122, %123) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"() [^125] : () -> ()
      ^125():
        %127 = "llvm.add"(%arg115_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%127) [^115] : (i64) -> ()
      ^119():
        "llvm.br"(%8) [^129] : (i64) -> ()
      ^129(%arg129_0 : i64):
        %131 = "llvm.icmp"(%arg129_0, %19) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%131) [^132, ^133] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^132():
        %135 = "llvm.sext"(%24) : (i32) -> i64
        %136 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %137 = "llvm.load"(%136) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %138 = "llvm.sext"(%25) : (i32) -> i64
        %139 = "llvm.getelementptr"(%arg7_5, %138) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %140 = "llvm.load"(%139) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %141 = "llvm.add"(%140, %137) : (i32, i32) -> i32
        "llvm.store"(%141, %139) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %144 = "llvm.getelementptr"(%arg7_5, %138) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %145 = "llvm.load"(%144) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %146 = "llvm.sext"(%26) : (i32) -> i64
        %147 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %148 = "llvm.load"(%147) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %149 = "llvm.xor"(%148, %145) : (i32, i32) -> i32
        "llvm.store"(%149, %147) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %152 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %153 = "llvm.load"(%152) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %154 = "llvm.shl"(%153, %22) : (i32, i32) -> i32
        %155 = "llvm.sub"(%27, %22) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %156 = "llvm.lshr"(%153, %155) : (i32, i32) -> i32
        %157 = "llvm.or"(%154, %156) : (i32, i32) -> i32
        %159 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%157, %159) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %162 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %163 = "llvm.load"(%162) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %164 = "llvm.sext"(%21) : (i32) -> i64
        %165 = "llvm.getelementptr"(%arg7_5, %164) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %166 = "llvm.load"(%165) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %167 = "llvm.add"(%166, %163) : (i32, i32) -> i32
        "llvm.store"(%167, %165) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %170 = "llvm.getelementptr"(%arg7_5, %164) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %171 = "llvm.load"(%170) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %173 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %174 = "llvm.load"(%173) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %175 = "llvm.xor"(%174, %171) : (i32, i32) -> i32
        "llvm.store"(%175, %173) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %178 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %179 = "llvm.load"(%178) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %180 = "llvm.shl"(%179, %26) : (i32, i32) -> i32
        %181 = "llvm.sub"(%27, %26) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %182 = "llvm.lshr"(%179, %181) : (i32, i32) -> i32
        %183 = "llvm.or"(%180, %182) : (i32, i32) -> i32
        %185 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%183, %185) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %188 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %189 = "llvm.load"(%188) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %191 = "llvm.getelementptr"(%arg7_5, %138) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %192 = "llvm.load"(%191) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %193 = "llvm.add"(%192, %189) : (i32, i32) -> i32
        "llvm.store"(%193, %191) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %196 = "llvm.getelementptr"(%arg7_5, %138) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %197 = "llvm.load"(%196) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %199 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %200 = "llvm.load"(%199) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %201 = "llvm.xor"(%200, %197) : (i32, i32) -> i32
        "llvm.store"(%201, %199) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %204 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %205 = "llvm.load"(%204) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %206 = "llvm.shl"(%205, %21) : (i32, i32) -> i32
        %207 = "llvm.sub"(%27, %21) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %208 = "llvm.lshr"(%205, %207) : (i32, i32) -> i32
        %209 = "llvm.or"(%206, %208) : (i32, i32) -> i32
        %211 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%209, %211) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %214 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %215 = "llvm.load"(%214) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %217 = "llvm.getelementptr"(%arg7_5, %164) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %218 = "llvm.load"(%217) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %219 = "llvm.add"(%218, %215) : (i32, i32) -> i32
        "llvm.store"(%219, %217) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %222 = "llvm.getelementptr"(%arg7_5, %164) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %223 = "llvm.load"(%222) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %225 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %226 = "llvm.load"(%225) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %227 = "llvm.xor"(%226, %223) : (i32, i32) -> i32
        "llvm.store"(%227, %225) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %230 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %231 = "llvm.load"(%230) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %232 = "llvm.shl"(%231, %28) : (i32, i32) -> i32
        %233 = "llvm.sub"(%27, %28) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %234 = "llvm.lshr"(%231, %233) : (i32, i32) -> i32
        %235 = "llvm.or"(%232, %234) : (i32, i32) -> i32
        %237 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%235, %237) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %239 = "llvm.sext"(%29) : (i32) -> i64
        %240 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %241 = "llvm.load"(%240) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %242 = "llvm.sext"(%30) : (i32) -> i64
        %243 = "llvm.getelementptr"(%arg7_5, %242) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %244 = "llvm.load"(%243) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %245 = "llvm.add"(%244, %241) : (i32, i32) -> i32
        "llvm.store"(%245, %243) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %248 = "llvm.getelementptr"(%arg7_5, %242) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %249 = "llvm.load"(%248) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %250 = "llvm.sext"(%31) : (i32) -> i64
        %251 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %252 = "llvm.load"(%251) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %253 = "llvm.xor"(%252, %249) : (i32, i32) -> i32
        "llvm.store"(%253, %251) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %256 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %257 = "llvm.load"(%256) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %258 = "llvm.shl"(%257, %22) : (i32, i32) -> i32
        %260 = "llvm.lshr"(%257, %155) : (i32, i32) -> i32
        %261 = "llvm.or"(%258, %260) : (i32, i32) -> i32
        %263 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%261, %263) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %266 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %267 = "llvm.load"(%266) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %268 = "llvm.sext"(%32) : (i32) -> i64
        %269 = "llvm.getelementptr"(%arg7_5, %268) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %270 = "llvm.load"(%269) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %271 = "llvm.add"(%270, %267) : (i32, i32) -> i32
        "llvm.store"(%271, %269) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %274 = "llvm.getelementptr"(%arg7_5, %268) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %275 = "llvm.load"(%274) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %277 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %278 = "llvm.load"(%277) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %279 = "llvm.xor"(%278, %275) : (i32, i32) -> i32
        "llvm.store"(%279, %277) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %282 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %283 = "llvm.load"(%282) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %284 = "llvm.shl"(%283, %26) : (i32, i32) -> i32
        %286 = "llvm.lshr"(%283, %181) : (i32, i32) -> i32
        %287 = "llvm.or"(%284, %286) : (i32, i32) -> i32
        %289 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%287, %289) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %292 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %293 = "llvm.load"(%292) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %295 = "llvm.getelementptr"(%arg7_5, %242) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %296 = "llvm.load"(%295) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %297 = "llvm.add"(%296, %293) : (i32, i32) -> i32
        "llvm.store"(%297, %295) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %300 = "llvm.getelementptr"(%arg7_5, %242) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %301 = "llvm.load"(%300) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %303 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %304 = "llvm.load"(%303) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %305 = "llvm.xor"(%304, %301) : (i32, i32) -> i32
        "llvm.store"(%305, %303) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %308 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %309 = "llvm.load"(%308) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %310 = "llvm.shl"(%309, %21) : (i32, i32) -> i32
        %312 = "llvm.lshr"(%309, %207) : (i32, i32) -> i32
        %313 = "llvm.or"(%310, %312) : (i32, i32) -> i32
        %315 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%313, %315) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %318 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %319 = "llvm.load"(%318) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %321 = "llvm.getelementptr"(%arg7_5, %268) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %322 = "llvm.load"(%321) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %323 = "llvm.add"(%322, %319) : (i32, i32) -> i32
        "llvm.store"(%323, %321) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %326 = "llvm.getelementptr"(%arg7_5, %268) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %327 = "llvm.load"(%326) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %329 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %330 = "llvm.load"(%329) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %331 = "llvm.xor"(%330, %327) : (i32, i32) -> i32
        "llvm.store"(%331, %329) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %334 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %335 = "llvm.load"(%334) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %336 = "llvm.shl"(%335, %28) : (i32, i32) -> i32
        %338 = "llvm.lshr"(%335, %233) : (i32, i32) -> i32
        %339 = "llvm.or"(%336, %338) : (i32, i32) -> i32
        %341 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%339, %341) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %343 = "llvm.sext"(%33) : (i32) -> i64
        %344 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %345 = "llvm.load"(%344) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %346 = "llvm.sext"(%34) : (i32) -> i64
        %347 = "llvm.getelementptr"(%arg7_5, %346) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %348 = "llvm.load"(%347) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %349 = "llvm.add"(%348, %345) : (i32, i32) -> i32
        "llvm.store"(%349, %347) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %352 = "llvm.getelementptr"(%arg7_5, %346) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %353 = "llvm.load"(%352) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %354 = "llvm.sext"(%35) : (i32) -> i64
        %355 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %356 = "llvm.load"(%355) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %357 = "llvm.xor"(%356, %353) : (i32, i32) -> i32
        "llvm.store"(%357, %355) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %360 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %361 = "llvm.load"(%360) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %362 = "llvm.shl"(%361, %22) : (i32, i32) -> i32
        %364 = "llvm.lshr"(%361, %155) : (i32, i32) -> i32
        %365 = "llvm.or"(%362, %364) : (i32, i32) -> i32
        %367 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%365, %367) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %370 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %371 = "llvm.load"(%370) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %372 = "llvm.sext"(%36) : (i32) -> i64
        %373 = "llvm.getelementptr"(%arg7_5, %372) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %374 = "llvm.load"(%373) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %375 = "llvm.add"(%374, %371) : (i32, i32) -> i32
        "llvm.store"(%375, %373) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %378 = "llvm.getelementptr"(%arg7_5, %372) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %379 = "llvm.load"(%378) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %381 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %382 = "llvm.load"(%381) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %383 = "llvm.xor"(%382, %379) : (i32, i32) -> i32
        "llvm.store"(%383, %381) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %386 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %387 = "llvm.load"(%386) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %388 = "llvm.shl"(%387, %26) : (i32, i32) -> i32
        %390 = "llvm.lshr"(%387, %181) : (i32, i32) -> i32
        %391 = "llvm.or"(%388, %390) : (i32, i32) -> i32
        %393 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%391, %393) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %396 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %397 = "llvm.load"(%396) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %399 = "llvm.getelementptr"(%arg7_5, %346) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %400 = "llvm.load"(%399) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %401 = "llvm.add"(%400, %397) : (i32, i32) -> i32
        "llvm.store"(%401, %399) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %404 = "llvm.getelementptr"(%arg7_5, %346) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %405 = "llvm.load"(%404) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %407 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %408 = "llvm.load"(%407) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %409 = "llvm.xor"(%408, %405) : (i32, i32) -> i32
        "llvm.store"(%409, %407) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %412 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %413 = "llvm.load"(%412) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %414 = "llvm.shl"(%413, %21) : (i32, i32) -> i32
        %416 = "llvm.lshr"(%413, %207) : (i32, i32) -> i32
        %417 = "llvm.or"(%414, %416) : (i32, i32) -> i32
        %419 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%417, %419) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %422 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %423 = "llvm.load"(%422) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %425 = "llvm.getelementptr"(%arg7_5, %372) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %426 = "llvm.load"(%425) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %427 = "llvm.add"(%426, %423) : (i32, i32) -> i32
        "llvm.store"(%427, %425) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %430 = "llvm.getelementptr"(%arg7_5, %372) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %431 = "llvm.load"(%430) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %433 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %434 = "llvm.load"(%433) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %435 = "llvm.xor"(%434, %431) : (i32, i32) -> i32
        "llvm.store"(%435, %433) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %438 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %439 = "llvm.load"(%438) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %440 = "llvm.shl"(%439, %28) : (i32, i32) -> i32
        %442 = "llvm.lshr"(%439, %233) : (i32, i32) -> i32
        %443 = "llvm.or"(%440, %442) : (i32, i32) -> i32
        %445 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%443, %445) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %447 = "llvm.sext"(%28) : (i32) -> i64
        %448 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %449 = "llvm.load"(%448) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %450 = "llvm.sext"(%37) : (i32) -> i64
        %451 = "llvm.getelementptr"(%arg7_5, %450) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %452 = "llvm.load"(%451) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %453 = "llvm.add"(%452, %449) : (i32, i32) -> i32
        "llvm.store"(%453, %451) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %456 = "llvm.getelementptr"(%arg7_5, %450) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %457 = "llvm.load"(%456) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %458 = "llvm.sext"(%38) : (i32) -> i64
        %459 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %460 = "llvm.load"(%459) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %461 = "llvm.xor"(%460, %457) : (i32, i32) -> i32
        "llvm.store"(%461, %459) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %464 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %465 = "llvm.load"(%464) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %466 = "llvm.shl"(%465, %22) : (i32, i32) -> i32
        %468 = "llvm.lshr"(%465, %155) : (i32, i32) -> i32
        %469 = "llvm.or"(%466, %468) : (i32, i32) -> i32
        %471 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%469, %471) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %474 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %475 = "llvm.load"(%474) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %476 = "llvm.sext"(%39) : (i32) -> i64
        %477 = "llvm.getelementptr"(%arg7_5, %476) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %478 = "llvm.load"(%477) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %479 = "llvm.add"(%478, %475) : (i32, i32) -> i32
        "llvm.store"(%479, %477) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %482 = "llvm.getelementptr"(%arg7_5, %476) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %483 = "llvm.load"(%482) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %485 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %486 = "llvm.load"(%485) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %487 = "llvm.xor"(%486, %483) : (i32, i32) -> i32
        "llvm.store"(%487, %485) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %490 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %491 = "llvm.load"(%490) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %492 = "llvm.shl"(%491, %26) : (i32, i32) -> i32
        %494 = "llvm.lshr"(%491, %181) : (i32, i32) -> i32
        %495 = "llvm.or"(%492, %494) : (i32, i32) -> i32
        %497 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%495, %497) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %500 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %501 = "llvm.load"(%500) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %503 = "llvm.getelementptr"(%arg7_5, %450) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %504 = "llvm.load"(%503) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %505 = "llvm.add"(%504, %501) : (i32, i32) -> i32
        "llvm.store"(%505, %503) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %508 = "llvm.getelementptr"(%arg7_5, %450) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %509 = "llvm.load"(%508) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %511 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %512 = "llvm.load"(%511) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %513 = "llvm.xor"(%512, %509) : (i32, i32) -> i32
        "llvm.store"(%513, %511) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %516 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %517 = "llvm.load"(%516) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %518 = "llvm.shl"(%517, %21) : (i32, i32) -> i32
        %520 = "llvm.lshr"(%517, %207) : (i32, i32) -> i32
        %521 = "llvm.or"(%518, %520) : (i32, i32) -> i32
        %523 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%521, %523) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %526 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %527 = "llvm.load"(%526) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %529 = "llvm.getelementptr"(%arg7_5, %476) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %530 = "llvm.load"(%529) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %531 = "llvm.add"(%530, %527) : (i32, i32) -> i32
        "llvm.store"(%531, %529) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %534 = "llvm.getelementptr"(%arg7_5, %476) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %535 = "llvm.load"(%534) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %537 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %538 = "llvm.load"(%537) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %539 = "llvm.xor"(%538, %535) : (i32, i32) -> i32
        "llvm.store"(%539, %537) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %542 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %543 = "llvm.load"(%542) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %544 = "llvm.shl"(%543, %28) : (i32, i32) -> i32
        %546 = "llvm.lshr"(%543, %233) : (i32, i32) -> i32
        %547 = "llvm.or"(%544, %546) : (i32, i32) -> i32
        %549 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%547, %549) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %552 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %553 = "llvm.load"(%552) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %555 = "llvm.getelementptr"(%arg7_5, %138) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %556 = "llvm.load"(%555) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %557 = "llvm.add"(%556, %553) : (i32, i32) -> i32
        "llvm.store"(%557, %555) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %560 = "llvm.getelementptr"(%arg7_5, %138) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %561 = "llvm.load"(%560) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %563 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %564 = "llvm.load"(%563) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %565 = "llvm.xor"(%564, %561) : (i32, i32) -> i32
        "llvm.store"(%565, %563) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %568 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %569 = "llvm.load"(%568) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %570 = "llvm.shl"(%569, %22) : (i32, i32) -> i32
        %572 = "llvm.lshr"(%569, %155) : (i32, i32) -> i32
        %573 = "llvm.or"(%570, %572) : (i32, i32) -> i32
        %575 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%573, %575) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %578 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %579 = "llvm.load"(%578) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %581 = "llvm.getelementptr"(%arg7_5, %372) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %582 = "llvm.load"(%581) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %583 = "llvm.add"(%582, %579) : (i32, i32) -> i32
        "llvm.store"(%583, %581) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %586 = "llvm.getelementptr"(%arg7_5, %372) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %587 = "llvm.load"(%586) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %589 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %590 = "llvm.load"(%589) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %591 = "llvm.xor"(%590, %587) : (i32, i32) -> i32
        "llvm.store"(%591, %589) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %594 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %595 = "llvm.load"(%594) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %596 = "llvm.shl"(%595, %26) : (i32, i32) -> i32
        %598 = "llvm.lshr"(%595, %181) : (i32, i32) -> i32
        %599 = "llvm.or"(%596, %598) : (i32, i32) -> i32
        %601 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%599, %601) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %604 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %605 = "llvm.load"(%604) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %607 = "llvm.getelementptr"(%arg7_5, %138) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %608 = "llvm.load"(%607) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %609 = "llvm.add"(%608, %605) : (i32, i32) -> i32
        "llvm.store"(%609, %607) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %612 = "llvm.getelementptr"(%arg7_5, %138) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %613 = "llvm.load"(%612) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %615 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %616 = "llvm.load"(%615) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %617 = "llvm.xor"(%616, %613) : (i32, i32) -> i32
        "llvm.store"(%617, %615) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %620 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %621 = "llvm.load"(%620) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %622 = "llvm.shl"(%621, %21) : (i32, i32) -> i32
        %624 = "llvm.lshr"(%621, %207) : (i32, i32) -> i32
        %625 = "llvm.or"(%622, %624) : (i32, i32) -> i32
        %627 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%625, %627) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %630 = "llvm.getelementptr"(%arg7_5, %458) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %631 = "llvm.load"(%630) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %633 = "llvm.getelementptr"(%arg7_5, %372) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %634 = "llvm.load"(%633) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %635 = "llvm.add"(%634, %631) : (i32, i32) -> i32
        "llvm.store"(%635, %633) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %638 = "llvm.getelementptr"(%arg7_5, %372) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %639 = "llvm.load"(%638) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %641 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %642 = "llvm.load"(%641) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %643 = "llvm.xor"(%642, %639) : (i32, i32) -> i32
        "llvm.store"(%643, %641) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %646 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %647 = "llvm.load"(%646) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %648 = "llvm.shl"(%647, %28) : (i32, i32) -> i32
        %650 = "llvm.lshr"(%647, %233) : (i32, i32) -> i32
        %651 = "llvm.or"(%648, %650) : (i32, i32) -> i32
        %653 = "llvm.getelementptr"(%arg7_5, %239) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%651, %653) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %656 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %657 = "llvm.load"(%656) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %659 = "llvm.getelementptr"(%arg7_5, %242) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %660 = "llvm.load"(%659) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %661 = "llvm.add"(%660, %657) : (i32, i32) -> i32
        "llvm.store"(%661, %659) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %664 = "llvm.getelementptr"(%arg7_5, %242) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %665 = "llvm.load"(%664) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %667 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %668 = "llvm.load"(%667) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %669 = "llvm.xor"(%668, %665) : (i32, i32) -> i32
        "llvm.store"(%669, %667) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %672 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %673 = "llvm.load"(%672) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %674 = "llvm.shl"(%673, %22) : (i32, i32) -> i32
        %676 = "llvm.lshr"(%673, %155) : (i32, i32) -> i32
        %677 = "llvm.or"(%674, %676) : (i32, i32) -> i32
        %679 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%677, %679) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %682 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %683 = "llvm.load"(%682) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %685 = "llvm.getelementptr"(%arg7_5, %476) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %686 = "llvm.load"(%685) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %687 = "llvm.add"(%686, %683) : (i32, i32) -> i32
        "llvm.store"(%687, %685) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %690 = "llvm.getelementptr"(%arg7_5, %476) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %691 = "llvm.load"(%690) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %693 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %694 = "llvm.load"(%693) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %695 = "llvm.xor"(%694, %691) : (i32, i32) -> i32
        "llvm.store"(%695, %693) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %698 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %699 = "llvm.load"(%698) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %700 = "llvm.shl"(%699, %26) : (i32, i32) -> i32
        %702 = "llvm.lshr"(%699, %181) : (i32, i32) -> i32
        %703 = "llvm.or"(%700, %702) : (i32, i32) -> i32
        %705 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%703, %705) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %708 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %709 = "llvm.load"(%708) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %711 = "llvm.getelementptr"(%arg7_5, %242) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %712 = "llvm.load"(%711) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %713 = "llvm.add"(%712, %709) : (i32, i32) -> i32
        "llvm.store"(%713, %711) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %716 = "llvm.getelementptr"(%arg7_5, %242) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %717 = "llvm.load"(%716) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %719 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %720 = "llvm.load"(%719) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %721 = "llvm.xor"(%720, %717) : (i32, i32) -> i32
        "llvm.store"(%721, %719) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %724 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %725 = "llvm.load"(%724) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %726 = "llvm.shl"(%725, %21) : (i32, i32) -> i32
        %728 = "llvm.lshr"(%725, %207) : (i32, i32) -> i32
        %729 = "llvm.or"(%726, %728) : (i32, i32) -> i32
        %731 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%729, %731) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %734 = "llvm.getelementptr"(%arg7_5, %146) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %735 = "llvm.load"(%734) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %737 = "llvm.getelementptr"(%arg7_5, %476) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %738 = "llvm.load"(%737) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %739 = "llvm.add"(%738, %735) : (i32, i32) -> i32
        "llvm.store"(%739, %737) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %742 = "llvm.getelementptr"(%arg7_5, %476) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %743 = "llvm.load"(%742) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %745 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %746 = "llvm.load"(%745) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %747 = "llvm.xor"(%746, %743) : (i32, i32) -> i32
        "llvm.store"(%747, %745) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %750 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %751 = "llvm.load"(%750) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %752 = "llvm.shl"(%751, %28) : (i32, i32) -> i32
        %754 = "llvm.lshr"(%751, %233) : (i32, i32) -> i32
        %755 = "llvm.or"(%752, %754) : (i32, i32) -> i32
        %757 = "llvm.getelementptr"(%arg7_5, %343) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%755, %757) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %760 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %761 = "llvm.load"(%760) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %763 = "llvm.getelementptr"(%arg7_5, %346) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %764 = "llvm.load"(%763) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %765 = "llvm.add"(%764, %761) : (i32, i32) -> i32
        "llvm.store"(%765, %763) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %768 = "llvm.getelementptr"(%arg7_5, %346) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %769 = "llvm.load"(%768) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %771 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %772 = "llvm.load"(%771) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %773 = "llvm.xor"(%772, %769) : (i32, i32) -> i32
        "llvm.store"(%773, %771) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %776 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %777 = "llvm.load"(%776) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %778 = "llvm.shl"(%777, %22) : (i32, i32) -> i32
        %780 = "llvm.lshr"(%777, %155) : (i32, i32) -> i32
        %781 = "llvm.or"(%778, %780) : (i32, i32) -> i32
        %783 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%781, %783) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %786 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %787 = "llvm.load"(%786) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %789 = "llvm.getelementptr"(%arg7_5, %164) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %790 = "llvm.load"(%789) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %791 = "llvm.add"(%790, %787) : (i32, i32) -> i32
        "llvm.store"(%791, %789) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %794 = "llvm.getelementptr"(%arg7_5, %164) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %795 = "llvm.load"(%794) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %797 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %798 = "llvm.load"(%797) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %799 = "llvm.xor"(%798, %795) : (i32, i32) -> i32
        "llvm.store"(%799, %797) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %802 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %803 = "llvm.load"(%802) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %804 = "llvm.shl"(%803, %26) : (i32, i32) -> i32
        %806 = "llvm.lshr"(%803, %181) : (i32, i32) -> i32
        %807 = "llvm.or"(%804, %806) : (i32, i32) -> i32
        %809 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%807, %809) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %812 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %813 = "llvm.load"(%812) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %815 = "llvm.getelementptr"(%arg7_5, %346) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %816 = "llvm.load"(%815) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %817 = "llvm.add"(%816, %813) : (i32, i32) -> i32
        "llvm.store"(%817, %815) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %820 = "llvm.getelementptr"(%arg7_5, %346) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %821 = "llvm.load"(%820) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %823 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %824 = "llvm.load"(%823) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %825 = "llvm.xor"(%824, %821) : (i32, i32) -> i32
        "llvm.store"(%825, %823) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %828 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %829 = "llvm.load"(%828) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %830 = "llvm.shl"(%829, %21) : (i32, i32) -> i32
        %832 = "llvm.lshr"(%829, %207) : (i32, i32) -> i32
        %833 = "llvm.or"(%830, %832) : (i32, i32) -> i32
        %835 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%833, %835) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %838 = "llvm.getelementptr"(%arg7_5, %250) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %839 = "llvm.load"(%838) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %841 = "llvm.getelementptr"(%arg7_5, %164) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %842 = "llvm.load"(%841) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %843 = "llvm.add"(%842, %839) : (i32, i32) -> i32
        "llvm.store"(%843, %841) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %846 = "llvm.getelementptr"(%arg7_5, %164) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %847 = "llvm.load"(%846) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %849 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %850 = "llvm.load"(%849) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %851 = "llvm.xor"(%850, %847) : (i32, i32) -> i32
        "llvm.store"(%851, %849) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %854 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %855 = "llvm.load"(%854) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %856 = "llvm.shl"(%855, %28) : (i32, i32) -> i32
        %858 = "llvm.lshr"(%855, %233) : (i32, i32) -> i32
        %859 = "llvm.or"(%856, %858) : (i32, i32) -> i32
        %861 = "llvm.getelementptr"(%arg7_5, %447) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%859, %861) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %864 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %865 = "llvm.load"(%864) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %867 = "llvm.getelementptr"(%arg7_5, %450) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %868 = "llvm.load"(%867) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %869 = "llvm.add"(%868, %865) : (i32, i32) -> i32
        "llvm.store"(%869, %867) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %872 = "llvm.getelementptr"(%arg7_5, %450) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %873 = "llvm.load"(%872) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %875 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %876 = "llvm.load"(%875) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %877 = "llvm.xor"(%876, %873) : (i32, i32) -> i32
        "llvm.store"(%877, %875) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %880 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %881 = "llvm.load"(%880) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %882 = "llvm.shl"(%881, %22) : (i32, i32) -> i32
        %884 = "llvm.lshr"(%881, %155) : (i32, i32) -> i32
        %885 = "llvm.or"(%882, %884) : (i32, i32) -> i32
        %887 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%885, %887) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %890 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %891 = "llvm.load"(%890) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %893 = "llvm.getelementptr"(%arg7_5, %268) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %894 = "llvm.load"(%893) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %895 = "llvm.add"(%894, %891) : (i32, i32) -> i32
        "llvm.store"(%895, %893) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %898 = "llvm.getelementptr"(%arg7_5, %268) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %899 = "llvm.load"(%898) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %901 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %902 = "llvm.load"(%901) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %903 = "llvm.xor"(%902, %899) : (i32, i32) -> i32
        "llvm.store"(%903, %901) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %906 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %907 = "llvm.load"(%906) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %908 = "llvm.shl"(%907, %26) : (i32, i32) -> i32
        %910 = "llvm.lshr"(%907, %181) : (i32, i32) -> i32
        %911 = "llvm.or"(%908, %910) : (i32, i32) -> i32
        %913 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%911, %913) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %916 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %917 = "llvm.load"(%916) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %919 = "llvm.getelementptr"(%arg7_5, %450) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %920 = "llvm.load"(%919) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %921 = "llvm.add"(%920, %917) : (i32, i32) -> i32
        "llvm.store"(%921, %919) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %924 = "llvm.getelementptr"(%arg7_5, %450) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %925 = "llvm.load"(%924) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %927 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %928 = "llvm.load"(%927) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %929 = "llvm.xor"(%928, %925) : (i32, i32) -> i32
        "llvm.store"(%929, %927) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %932 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %933 = "llvm.load"(%932) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %934 = "llvm.shl"(%933, %21) : (i32, i32) -> i32
        %936 = "llvm.lshr"(%933, %207) : (i32, i32) -> i32
        %937 = "llvm.or"(%934, %936) : (i32, i32) -> i32
        %939 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%937, %939) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %942 = "llvm.getelementptr"(%arg7_5, %354) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %943 = "llvm.load"(%942) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %945 = "llvm.getelementptr"(%arg7_5, %268) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %946 = "llvm.load"(%945) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %947 = "llvm.add"(%946, %943) : (i32, i32) -> i32
        "llvm.store"(%947, %945) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %950 = "llvm.getelementptr"(%arg7_5, %268) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %951 = "llvm.load"(%950) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %953 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %954 = "llvm.load"(%953) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %955 = "llvm.xor"(%954, %951) : (i32, i32) -> i32
        "llvm.store"(%955, %953) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %958 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %959 = "llvm.load"(%958) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %960 = "llvm.shl"(%959, %28) : (i32, i32) -> i32
        %962 = "llvm.lshr"(%959, %233) : (i32, i32) -> i32
        %963 = "llvm.or"(%960, %962) : (i32, i32) -> i32
        %965 = "llvm.getelementptr"(%arg7_5, %135) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%963, %965) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"() [^967] : () -> ()
      ^967():
        %969 = "llvm.add"(%arg129_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%969) [^129] : (i64) -> ()
      ^133():
        "llvm.br"(%8) [^971] : (i64) -> ()
      ^971(%arg971_0 : i64):
        %973 = "llvm.icmp"(%arg971_0, %18) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%973) [^974, ^975] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^974():
        %977 = "llvm.mul"(%20, %arg971_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %978 = "llvm.getelementptr"(%arg7_3, %977) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %979 = "llvm.getelementptr"(%arg7_5, %arg971_0) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %980 = "llvm.load"(%979) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %981 = "llvm.getelementptr"(%arg7_4, %arg971_0) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %982 = "llvm.load"(%981) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %983 = "llvm.add"(%980, %982) : (i32, i32) -> i32
        %984 = "llvm.trunc"(%983) : (i32) -> i8
        "llvm.store"(%984, %978) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %986 = "llvm.lshr"(%983, %21) : (i32, i32) -> i32
        %987 = "llvm.trunc"(%986) : (i32) -> i8
        %988 = "llvm.getelementptr"(%978, %10) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%987, %988) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %990 = "llvm.lshr"(%983, %22) : (i32, i32) -> i32
        %991 = "llvm.trunc"(%990) : (i32) -> i8
        %992 = "llvm.getelementptr"(%978, %12) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%991, %992) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        %994 = "llvm.lshr"(%983, %23) : (i32, i32) -> i32
        %995 = "llvm.trunc"(%994) : (i32) -> i8
        %996 = "llvm.getelementptr"(%978, %14) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%995, %996) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
        "llvm.br"() [^998] : () -> ()
      ^998():
        %1000 = "llvm.add"(%arg971_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%1000) [^971] : (i64) -> ()
      ^975():
        "llvm.return"() : () -> ()
    }) : () -> ()
}) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "o", "dlti.legal_int_widths" = array<i32: 32, 64>, "dlti.stack_alignment" = 128 : i64, "dlti.function_pointer_alignment" = #dlti.function_pointer_alignment<32, function_dependent = true>>, "llvm.ident" = "Homebrew clang version 22.1.7", "llvm.module_asm" = [], "llvm.target_triple" = "arm64-apple-macosx26.0.0"} : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^[[bb4:[0-9]+]]():
// CHECK-NEXT:     "llvm.module_flags"() {{.*}} : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}"sym_name" = "chacha20_block"{{.*}}}> ({
// CHECK-NEXT:       ^[[bb7:[0-9]+]](%[[varg7_0:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_1:[a-zA-Z0-9_]+]] : i32, %[[varg7_2:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_3:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_4:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_5:[a-zA-Z0-9_]+]] : !llvm.ptr):
// CHECK-NEXT:         %[[v8:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:         %[[v9:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1634760805 : i32}> : () -> i32
// CHECK-NEXT:         %[[v10:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[v11:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 857760878 : i32}> : () -> i32
// CHECK-NEXT:         %[[v12:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:         %[[v13:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2036477234 : i32}> : () -> i32
// CHECK-NEXT:         %[[v14:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK-NEXT:         %[[v15:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1797285236 : i32}> : () -> i32
// CHECK-NEXT:         %[[v16:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 8 : i64}> : () -> i64
// CHECK-NEXT:         %[[v17:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 12 : i64}> : () -> i64
// CHECK-NEXT:         %[[v18:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 16 : i64}> : () -> i64
// CHECK-NEXT:         %[[v19:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 10 : i64}> : () -> i64
// CHECK-NEXT:         %[[v20:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
// CHECK-NEXT:         %[[v21:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
// CHECK-NEXT:         %[[v22:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
// CHECK-NEXT:         %[[v23:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 24 : i32}> : () -> i32
// CHECK-NEXT:         %[[v24:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
// CHECK-NEXT:         %[[v25:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         %[[v26:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK-NEXT:         %[[v27:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
// CHECK-NEXT:         %[[v28:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:         %[[v29:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK-NEXT:         %[[v30:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v31:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:         %[[v32:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 9 : i32}> : () -> i32
// CHECK-NEXT:         %[[v33:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
// CHECK-NEXT:         %[[v34:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// CHECK-NEXT:         %[[v35:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 14 : i32}> : () -> i32
// CHECK-NEXT:         %[[v36:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
// CHECK-NEXT:         %[[v37:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:         %[[v38:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
// CHECK-NEXT:         %[[v39:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
// CHECK-NEXT:         %[[v40:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 13 : i64}> : () -> i64
// CHECK-NEXT:         %[[v41:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v8]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v9]], %[[v41]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v43:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v10]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v11]], %[[v43]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v45:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v12]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v13]], %[[v45]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v47:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v14]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v15]], %[[v47]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb49:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb49]](%[[varg49_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v51:[0-9]+]] = "llvm.icmp"(%[[varg49_0]], %[[v16]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v51]]) [^[[bb52:[0-9]+]], ^[[bb53:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb52]]():
// CHECK-NEXT:         %[[v55:[0-9]+]] = "llvm.mul"(%[[v20]], %[[varg49_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v56:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v55]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v57:[0-9]+]] = "llvm.load"(%[[v56]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v58:[0-9]+]] = "llvm.zext"(%[[v57]]) : (i8) -> i32
// CHECK-NEXT:         %[[v59:[0-9]+]] = "llvm.getelementptr"(%[[v56]], %[[v10]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v60:[0-9]+]] = "llvm.load"(%[[v59]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v61:[0-9]+]] = "llvm.zext"(%[[v60]]) : (i8) -> i32
// CHECK-NEXT:         %[[v62:[0-9]+]] = "llvm.shl"(%[[v61]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v63:[0-9]+]] = "llvm.or"(%[[v58]], %[[v62]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v64:[0-9]+]] = "llvm.getelementptr"(%[[v56]], %[[v12]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v65:[0-9]+]] = "llvm.load"(%[[v64]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v66:[0-9]+]] = "llvm.zext"(%[[v65]]) : (i8) -> i32
// CHECK-NEXT:         %[[v67:[0-9]+]] = "llvm.shl"(%[[v66]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v68:[0-9]+]] = "llvm.or"(%[[v63]], %[[v67]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v69:[0-9]+]] = "llvm.getelementptr"(%[[v56]], %[[v14]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v70:[0-9]+]] = "llvm.load"(%[[v69]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v71:[0-9]+]] = "llvm.zext"(%[[v70]]) : (i8) -> i32
// CHECK-NEXT:         %[[v72:[0-9]+]] = "llvm.shl"(%[[v71]], %[[v23]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v73:[0-9]+]] = "llvm.or"(%[[v68]], %[[v72]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v74:[0-9]+]] = "llvm.add"(%[[v20]], %[[varg49_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v75:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v74]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v73]], %[[v75]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb77:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb77]]():
// CHECK-NEXT:         %[[v79:[0-9]+]] = "llvm.add"(%[[varg49_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v79]]) [^[[bb49]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb53]]():
// CHECK-NEXT:         %[[v81:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v17]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[varg7_1]], %[[v81]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb83:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb83]](%[[varg83_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v85:[0-9]+]] = "llvm.icmp"(%[[varg83_0]], %[[v14]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v85]]) [^[[bb86:[0-9]+]], ^[[bb87:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb86]]():
// CHECK-NEXT:         %[[v89:[0-9]+]] = "llvm.mul"(%[[v20]], %[[varg83_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v90:[0-9]+]] = "llvm.getelementptr"(%[[varg7_2]], %[[v89]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v91:[0-9]+]] = "llvm.load"(%[[v90]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v92:[0-9]+]] = "llvm.zext"(%[[v91]]) : (i8) -> i32
// CHECK-NEXT:         %[[v93:[0-9]+]] = "llvm.getelementptr"(%[[v90]], %[[v10]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v94:[0-9]+]] = "llvm.load"(%[[v93]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v95:[0-9]+]] = "llvm.zext"(%[[v94]]) : (i8) -> i32
// CHECK-NEXT:         %[[v96:[0-9]+]] = "llvm.shl"(%[[v95]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v97:[0-9]+]] = "llvm.or"(%[[v92]], %[[v96]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v98:[0-9]+]] = "llvm.getelementptr"(%[[v90]], %[[v12]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v99:[0-9]+]] = "llvm.load"(%[[v98]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v100:[0-9]+]] = "llvm.zext"(%[[v99]]) : (i8) -> i32
// CHECK-NEXT:         %[[v101:[0-9]+]] = "llvm.shl"(%[[v100]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v102:[0-9]+]] = "llvm.or"(%[[v97]], %[[v101]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v103:[0-9]+]] = "llvm.getelementptr"(%[[v90]], %[[v14]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v104:[0-9]+]] = "llvm.load"(%[[v103]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i8
// CHECK-NEXT:         %[[v105:[0-9]+]] = "llvm.zext"(%[[v104]]) : (i8) -> i32
// CHECK-NEXT:         %[[v106:[0-9]+]] = "llvm.shl"(%[[v105]], %[[v23]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v107:[0-9]+]] = "llvm.or"(%[[v102]], %[[v106]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v108:[0-9]+]] = "llvm.add"(%[[v40]], %[[varg83_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v109:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[v108]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v107]], %[[v109]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb111:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb111]]():
// CHECK-NEXT:         %[[v113:[0-9]+]] = "llvm.add"(%[[varg83_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v113]]) [^[[bb83]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb87]]():
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb115:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb115]](%[[varg115_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v117:[0-9]+]] = "llvm.icmp"(%[[varg115_0]], %[[v18]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v117]]) [^[[bb118:[0-9]+]], ^[[bb119:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb118]]():
// CHECK-NEXT:         %[[v121:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[varg115_0]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v122:[0-9]+]] = "llvm.load"(%[[v121]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v123:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[varg115_0]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v122]], %[[v123]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb125:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb125]]():
// CHECK-NEXT:         %[[v127:[0-9]+]] = "llvm.add"(%[[varg115_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v127]]) [^[[bb115]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb119]]():
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb129:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb129]](%[[varg129_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v131:[0-9]+]] = "llvm.icmp"(%[[varg129_0]], %[[v19]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v131]]) [^[[bb132:[0-9]+]], ^[[bb133:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb132]]():
// CHECK-NEXT:         %[[v135:[0-9]+]] = "llvm.sext"(%[[v24]]) : (i32) -> i64
// CHECK-NEXT:         %[[v136:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v137:[0-9]+]] = "llvm.load"(%[[v136]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v138:[0-9]+]] = "llvm.sext"(%[[v25]]) : (i32) -> i64
// CHECK-NEXT:         %[[v139:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v140:[0-9]+]] = "llvm.load"(%[[v139]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v141:[0-9]+]] = "llvm.add"(%[[v140]], %[[v137]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v141]], %[[v139]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v143:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v144:[0-9]+]] = "llvm.load"(%[[v143]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v145:[0-9]+]] = "llvm.sext"(%[[v26]]) : (i32) -> i64
// CHECK-NEXT:         %[[v146:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v147:[0-9]+]] = "llvm.load"(%[[v146]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v148:[0-9]+]] = "llvm.xor"(%[[v147]], %[[v144]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v148]], %[[v146]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v150:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v151:[0-9]+]] = "llvm.load"(%[[v150]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v152:[0-9]+]] = "llvm.shl"(%[[v151]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v153:[0-9]+]] = "llvm.sub"(%[[v27]], %[[v22]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v154:[0-9]+]] = "llvm.lshr"(%[[v151]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v155:[0-9]+]] = "llvm.or"(%[[v152]], %[[v154]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v156:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v155]], %[[v156]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v158:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v159:[0-9]+]] = "llvm.load"(%[[v158]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v160:[0-9]+]] = "llvm.sext"(%[[v21]]) : (i32) -> i64
// CHECK-NEXT:         %[[v161:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v160]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v162:[0-9]+]] = "llvm.load"(%[[v161]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v163:[0-9]+]] = "llvm.add"(%[[v162]], %[[v159]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v163]], %[[v161]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v165:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v160]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v166:[0-9]+]] = "llvm.load"(%[[v165]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v167:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v168:[0-9]+]] = "llvm.load"(%[[v167]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v169:[0-9]+]] = "llvm.xor"(%[[v168]], %[[v166]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v169]], %[[v167]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v171:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v172:[0-9]+]] = "llvm.load"(%[[v171]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v173:[0-9]+]] = "llvm.shl"(%[[v172]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v174:[0-9]+]] = "llvm.sub"(%[[v27]], %[[v26]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v175:[0-9]+]] = "llvm.lshr"(%[[v172]], %[[v174]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v176:[0-9]+]] = "llvm.or"(%[[v173]], %[[v175]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v177:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v176]], %[[v177]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v179:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v180:[0-9]+]] = "llvm.load"(%[[v179]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v181:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v182:[0-9]+]] = "llvm.load"(%[[v181]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v183:[0-9]+]] = "llvm.add"(%[[v182]], %[[v180]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v183]], %[[v181]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v185:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v186:[0-9]+]] = "llvm.load"(%[[v185]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v187:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v188:[0-9]+]] = "llvm.load"(%[[v187]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v189:[0-9]+]] = "llvm.xor"(%[[v188]], %[[v186]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v189]], %[[v187]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v191:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v192:[0-9]+]] = "llvm.load"(%[[v191]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v193:[0-9]+]] = "llvm.shl"(%[[v192]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v194:[0-9]+]] = "llvm.sub"(%[[v27]], %[[v21]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v195:[0-9]+]] = "llvm.lshr"(%[[v192]], %[[v194]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v196:[0-9]+]] = "llvm.or"(%[[v193]], %[[v195]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v197:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v196]], %[[v197]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v199:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v200:[0-9]+]] = "llvm.load"(%[[v199]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v201:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v160]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v202:[0-9]+]] = "llvm.load"(%[[v201]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v203:[0-9]+]] = "llvm.add"(%[[v202]], %[[v200]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v203]], %[[v201]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v205:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v160]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v206:[0-9]+]] = "llvm.load"(%[[v205]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v207:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v208:[0-9]+]] = "llvm.load"(%[[v207]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v209:[0-9]+]] = "llvm.xor"(%[[v208]], %[[v206]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v209]], %[[v207]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v211:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v212:[0-9]+]] = "llvm.load"(%[[v211]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v213:[0-9]+]] = "llvm.shl"(%[[v212]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v214:[0-9]+]] = "llvm.sub"(%[[v27]], %[[v28]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v215:[0-9]+]] = "llvm.lshr"(%[[v212]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v216:[0-9]+]] = "llvm.or"(%[[v213]], %[[v215]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v217:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v216]], %[[v217]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v219:[0-9]+]] = "llvm.sext"(%[[v29]]) : (i32) -> i64
// CHECK-NEXT:         %[[v220:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v221:[0-9]+]] = "llvm.load"(%[[v220]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v222:[0-9]+]] = "llvm.sext"(%[[v30]]) : (i32) -> i64
// CHECK-NEXT:         %[[v223:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v222]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v224:[0-9]+]] = "llvm.load"(%[[v223]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v225:[0-9]+]] = "llvm.add"(%[[v224]], %[[v221]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v225]], %[[v223]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v227:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v222]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v228:[0-9]+]] = "llvm.load"(%[[v227]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v229:[0-9]+]] = "llvm.sext"(%[[v31]]) : (i32) -> i64
// CHECK-NEXT:         %[[v230:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v231:[0-9]+]] = "llvm.load"(%[[v230]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v232:[0-9]+]] = "llvm.xor"(%[[v231]], %[[v228]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v232]], %[[v230]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v234:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v235:[0-9]+]] = "llvm.load"(%[[v234]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v236:[0-9]+]] = "llvm.shl"(%[[v235]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v237:[0-9]+]] = "llvm.lshr"(%[[v235]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v238:[0-9]+]] = "llvm.or"(%[[v236]], %[[v237]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v239:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v238]], %[[v239]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v241:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v242:[0-9]+]] = "llvm.load"(%[[v241]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v243:[0-9]+]] = "llvm.sext"(%[[v32]]) : (i32) -> i64
// CHECK-NEXT:         %[[v244:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v243]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v245:[0-9]+]] = "llvm.load"(%[[v244]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v246:[0-9]+]] = "llvm.add"(%[[v245]], %[[v242]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v246]], %[[v244]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v248:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v243]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v249:[0-9]+]] = "llvm.load"(%[[v248]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v250:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v251:[0-9]+]] = "llvm.load"(%[[v250]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v252:[0-9]+]] = "llvm.xor"(%[[v251]], %[[v249]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v252]], %[[v250]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v254:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v255:[0-9]+]] = "llvm.load"(%[[v254]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v256:[0-9]+]] = "llvm.shl"(%[[v255]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v257:[0-9]+]] = "llvm.lshr"(%[[v255]], %[[v174]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v258:[0-9]+]] = "llvm.or"(%[[v256]], %[[v257]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v259:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v258]], %[[v259]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v261:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v262:[0-9]+]] = "llvm.load"(%[[v261]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v263:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v222]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v264:[0-9]+]] = "llvm.load"(%[[v263]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v265:[0-9]+]] = "llvm.add"(%[[v264]], %[[v262]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v265]], %[[v263]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v267:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v222]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v268:[0-9]+]] = "llvm.load"(%[[v267]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v269:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v270:[0-9]+]] = "llvm.load"(%[[v269]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v271:[0-9]+]] = "llvm.xor"(%[[v270]], %[[v268]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v271]], %[[v269]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v273:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v274:[0-9]+]] = "llvm.load"(%[[v273]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v275:[0-9]+]] = "llvm.shl"(%[[v274]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v276:[0-9]+]] = "llvm.lshr"(%[[v274]], %[[v194]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v277:[0-9]+]] = "llvm.or"(%[[v275]], %[[v276]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v278:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v277]], %[[v278]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v280:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v281:[0-9]+]] = "llvm.load"(%[[v280]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v282:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v243]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v283:[0-9]+]] = "llvm.load"(%[[v282]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v284:[0-9]+]] = "llvm.add"(%[[v283]], %[[v281]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v284]], %[[v282]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v286:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v243]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v287:[0-9]+]] = "llvm.load"(%[[v286]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v288:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v289:[0-9]+]] = "llvm.load"(%[[v288]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v290:[0-9]+]] = "llvm.xor"(%[[v289]], %[[v287]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v290]], %[[v288]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v292:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v293:[0-9]+]] = "llvm.load"(%[[v292]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v294:[0-9]+]] = "llvm.shl"(%[[v293]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v295:[0-9]+]] = "llvm.lshr"(%[[v293]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v296:[0-9]+]] = "llvm.or"(%[[v294]], %[[v295]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v297:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v296]], %[[v297]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v299:[0-9]+]] = "llvm.sext"(%[[v33]]) : (i32) -> i64
// CHECK-NEXT:         %[[v300:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v301:[0-9]+]] = "llvm.load"(%[[v300]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v302:[0-9]+]] = "llvm.sext"(%[[v34]]) : (i32) -> i64
// CHECK-NEXT:         %[[v303:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v302]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v304:[0-9]+]] = "llvm.load"(%[[v303]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v305:[0-9]+]] = "llvm.add"(%[[v304]], %[[v301]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v305]], %[[v303]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v307:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v302]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v308:[0-9]+]] = "llvm.load"(%[[v307]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v309:[0-9]+]] = "llvm.sext"(%[[v35]]) : (i32) -> i64
// CHECK-NEXT:         %[[v310:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v311:[0-9]+]] = "llvm.load"(%[[v310]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v312:[0-9]+]] = "llvm.xor"(%[[v311]], %[[v308]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v312]], %[[v310]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v314:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v315:[0-9]+]] = "llvm.load"(%[[v314]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v316:[0-9]+]] = "llvm.shl"(%[[v315]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v317:[0-9]+]] = "llvm.lshr"(%[[v315]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v318:[0-9]+]] = "llvm.or"(%[[v316]], %[[v317]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v319:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v318]], %[[v319]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v321:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v322:[0-9]+]] = "llvm.load"(%[[v321]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v323:[0-9]+]] = "llvm.sext"(%[[v36]]) : (i32) -> i64
// CHECK-NEXT:         %[[v324:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v323]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v325:[0-9]+]] = "llvm.load"(%[[v324]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v326:[0-9]+]] = "llvm.add"(%[[v325]], %[[v322]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v326]], %[[v324]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v328:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v323]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v329:[0-9]+]] = "llvm.load"(%[[v328]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v330:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v331:[0-9]+]] = "llvm.load"(%[[v330]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v332:[0-9]+]] = "llvm.xor"(%[[v331]], %[[v329]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v332]], %[[v330]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v334:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v335:[0-9]+]] = "llvm.load"(%[[v334]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v336:[0-9]+]] = "llvm.shl"(%[[v335]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v337:[0-9]+]] = "llvm.lshr"(%[[v335]], %[[v174]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v338:[0-9]+]] = "llvm.or"(%[[v336]], %[[v337]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v339:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v338]], %[[v339]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v341:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v342:[0-9]+]] = "llvm.load"(%[[v341]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v343:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v302]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v344:[0-9]+]] = "llvm.load"(%[[v343]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v345:[0-9]+]] = "llvm.add"(%[[v344]], %[[v342]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v345]], %[[v343]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v347:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v302]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v348:[0-9]+]] = "llvm.load"(%[[v347]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v349:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v350:[0-9]+]] = "llvm.load"(%[[v349]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v351:[0-9]+]] = "llvm.xor"(%[[v350]], %[[v348]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v351]], %[[v349]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v353:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v354:[0-9]+]] = "llvm.load"(%[[v353]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v355:[0-9]+]] = "llvm.shl"(%[[v354]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v356:[0-9]+]] = "llvm.lshr"(%[[v354]], %[[v194]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v357:[0-9]+]] = "llvm.or"(%[[v355]], %[[v356]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v358:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v357]], %[[v358]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v360:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v361:[0-9]+]] = "llvm.load"(%[[v360]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v362:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v323]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v363:[0-9]+]] = "llvm.load"(%[[v362]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v364:[0-9]+]] = "llvm.add"(%[[v363]], %[[v361]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v364]], %[[v362]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v366:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v323]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v367:[0-9]+]] = "llvm.load"(%[[v366]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v368:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v369:[0-9]+]] = "llvm.load"(%[[v368]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v370:[0-9]+]] = "llvm.xor"(%[[v369]], %[[v367]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v370]], %[[v368]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v372:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v373:[0-9]+]] = "llvm.load"(%[[v372]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v374:[0-9]+]] = "llvm.shl"(%[[v373]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v375:[0-9]+]] = "llvm.lshr"(%[[v373]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v376:[0-9]+]] = "llvm.or"(%[[v374]], %[[v375]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v377:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v376]], %[[v377]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v379:[0-9]+]] = "llvm.sext"(%[[v28]]) : (i32) -> i64
// CHECK-NEXT:         %[[v380:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v381:[0-9]+]] = "llvm.load"(%[[v380]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v382:[0-9]+]] = "llvm.sext"(%[[v37]]) : (i32) -> i64
// CHECK-NEXT:         %[[v383:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v382]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v384:[0-9]+]] = "llvm.load"(%[[v383]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v385:[0-9]+]] = "llvm.add"(%[[v384]], %[[v381]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v385]], %[[v383]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v387:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v382]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v388:[0-9]+]] = "llvm.load"(%[[v387]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v389:[0-9]+]] = "llvm.sext"(%[[v38]]) : (i32) -> i64
// CHECK-NEXT:         %[[v390:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v391:[0-9]+]] = "llvm.load"(%[[v390]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v392:[0-9]+]] = "llvm.xor"(%[[v391]], %[[v388]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v392]], %[[v390]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v394:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v395:[0-9]+]] = "llvm.load"(%[[v394]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v396:[0-9]+]] = "llvm.shl"(%[[v395]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v397:[0-9]+]] = "llvm.lshr"(%[[v395]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v398:[0-9]+]] = "llvm.or"(%[[v396]], %[[v397]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v399:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v398]], %[[v399]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v401:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v402:[0-9]+]] = "llvm.load"(%[[v401]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v403:[0-9]+]] = "llvm.sext"(%[[v39]]) : (i32) -> i64
// CHECK-NEXT:         %[[v404:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v403]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v405:[0-9]+]] = "llvm.load"(%[[v404]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v406:[0-9]+]] = "llvm.add"(%[[v405]], %[[v402]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v406]], %[[v404]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v408:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v403]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v409:[0-9]+]] = "llvm.load"(%[[v408]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v410:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v411:[0-9]+]] = "llvm.load"(%[[v410]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v412:[0-9]+]] = "llvm.xor"(%[[v411]], %[[v409]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v412]], %[[v410]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v414:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v415:[0-9]+]] = "llvm.load"(%[[v414]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v416:[0-9]+]] = "llvm.shl"(%[[v415]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v417:[0-9]+]] = "llvm.lshr"(%[[v415]], %[[v174]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v418:[0-9]+]] = "llvm.or"(%[[v416]], %[[v417]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v419:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v418]], %[[v419]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v421:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v422:[0-9]+]] = "llvm.load"(%[[v421]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v423:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v382]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v424:[0-9]+]] = "llvm.load"(%[[v423]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v425:[0-9]+]] = "llvm.add"(%[[v424]], %[[v422]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v425]], %[[v423]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v427:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v382]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v428:[0-9]+]] = "llvm.load"(%[[v427]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v429:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v430:[0-9]+]] = "llvm.load"(%[[v429]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v431:[0-9]+]] = "llvm.xor"(%[[v430]], %[[v428]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v431]], %[[v429]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v433:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v434:[0-9]+]] = "llvm.load"(%[[v433]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v435:[0-9]+]] = "llvm.shl"(%[[v434]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v436:[0-9]+]] = "llvm.lshr"(%[[v434]], %[[v194]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v437:[0-9]+]] = "llvm.or"(%[[v435]], %[[v436]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v438:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v437]], %[[v438]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v440:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v441:[0-9]+]] = "llvm.load"(%[[v440]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v442:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v403]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v443:[0-9]+]] = "llvm.load"(%[[v442]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v444:[0-9]+]] = "llvm.add"(%[[v443]], %[[v441]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v444]], %[[v442]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v446:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v403]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v447:[0-9]+]] = "llvm.load"(%[[v446]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v448:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v449:[0-9]+]] = "llvm.load"(%[[v448]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v450:[0-9]+]] = "llvm.xor"(%[[v449]], %[[v447]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v450]], %[[v448]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v452:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v453:[0-9]+]] = "llvm.load"(%[[v452]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v454:[0-9]+]] = "llvm.shl"(%[[v453]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v455:[0-9]+]] = "llvm.lshr"(%[[v453]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v456:[0-9]+]] = "llvm.or"(%[[v454]], %[[v455]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v457:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v456]], %[[v457]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v459:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v460:[0-9]+]] = "llvm.load"(%[[v459]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v461:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v462:[0-9]+]] = "llvm.load"(%[[v461]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v463:[0-9]+]] = "llvm.add"(%[[v462]], %[[v460]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v463]], %[[v461]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v465:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v466:[0-9]+]] = "llvm.load"(%[[v465]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v467:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v468:[0-9]+]] = "llvm.load"(%[[v467]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v469:[0-9]+]] = "llvm.xor"(%[[v468]], %[[v466]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v469]], %[[v467]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v471:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v472:[0-9]+]] = "llvm.load"(%[[v471]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v473:[0-9]+]] = "llvm.shl"(%[[v472]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v474:[0-9]+]] = "llvm.lshr"(%[[v472]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v475:[0-9]+]] = "llvm.or"(%[[v473]], %[[v474]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v476:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v475]], %[[v476]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v478:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v479:[0-9]+]] = "llvm.load"(%[[v478]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v480:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v323]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v481:[0-9]+]] = "llvm.load"(%[[v480]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v482:[0-9]+]] = "llvm.add"(%[[v481]], %[[v479]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v482]], %[[v480]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v484:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v323]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v485:[0-9]+]] = "llvm.load"(%[[v484]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v486:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v487:[0-9]+]] = "llvm.load"(%[[v486]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v488:[0-9]+]] = "llvm.xor"(%[[v487]], %[[v485]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v488]], %[[v486]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v490:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v491:[0-9]+]] = "llvm.load"(%[[v490]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v492:[0-9]+]] = "llvm.shl"(%[[v491]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v493:[0-9]+]] = "llvm.lshr"(%[[v491]], %[[v174]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v494:[0-9]+]] = "llvm.or"(%[[v492]], %[[v493]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v495:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v494]], %[[v495]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v497:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v498:[0-9]+]] = "llvm.load"(%[[v497]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v499:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v500:[0-9]+]] = "llvm.load"(%[[v499]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v501:[0-9]+]] = "llvm.add"(%[[v500]], %[[v498]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v501]], %[[v499]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v503:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v138]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v504:[0-9]+]] = "llvm.load"(%[[v503]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v505:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v506:[0-9]+]] = "llvm.load"(%[[v505]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v507:[0-9]+]] = "llvm.xor"(%[[v506]], %[[v504]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v507]], %[[v505]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v509:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v510:[0-9]+]] = "llvm.load"(%[[v509]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v511:[0-9]+]] = "llvm.shl"(%[[v510]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v512:[0-9]+]] = "llvm.lshr"(%[[v510]], %[[v194]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v513:[0-9]+]] = "llvm.or"(%[[v511]], %[[v512]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v514:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v513]], %[[v514]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v516:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v389]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v517:[0-9]+]] = "llvm.load"(%[[v516]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v518:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v323]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v519:[0-9]+]] = "llvm.load"(%[[v518]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v520:[0-9]+]] = "llvm.add"(%[[v519]], %[[v517]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v520]], %[[v518]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v522:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v323]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v523:[0-9]+]] = "llvm.load"(%[[v522]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v524:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v525:[0-9]+]] = "llvm.load"(%[[v524]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v526:[0-9]+]] = "llvm.xor"(%[[v525]], %[[v523]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v526]], %[[v524]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v528:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v529:[0-9]+]] = "llvm.load"(%[[v528]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v530:[0-9]+]] = "llvm.shl"(%[[v529]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v531:[0-9]+]] = "llvm.lshr"(%[[v529]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v532:[0-9]+]] = "llvm.or"(%[[v530]], %[[v531]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v533:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v219]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v532]], %[[v533]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v535:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v536:[0-9]+]] = "llvm.load"(%[[v535]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v537:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v222]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v538:[0-9]+]] = "llvm.load"(%[[v537]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v539:[0-9]+]] = "llvm.add"(%[[v538]], %[[v536]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v539]], %[[v537]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v541:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v222]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v542:[0-9]+]] = "llvm.load"(%[[v541]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v543:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v544:[0-9]+]] = "llvm.load"(%[[v543]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v545:[0-9]+]] = "llvm.xor"(%[[v544]], %[[v542]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v545]], %[[v543]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v547:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v548:[0-9]+]] = "llvm.load"(%[[v547]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v549:[0-9]+]] = "llvm.shl"(%[[v548]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v550:[0-9]+]] = "llvm.lshr"(%[[v548]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v551:[0-9]+]] = "llvm.or"(%[[v549]], %[[v550]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v552:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v551]], %[[v552]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v554:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v555:[0-9]+]] = "llvm.load"(%[[v554]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v556:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v403]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v557:[0-9]+]] = "llvm.load"(%[[v556]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v558:[0-9]+]] = "llvm.add"(%[[v557]], %[[v555]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v558]], %[[v556]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v560:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v403]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v561:[0-9]+]] = "llvm.load"(%[[v560]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v562:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v563:[0-9]+]] = "llvm.load"(%[[v562]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v564:[0-9]+]] = "llvm.xor"(%[[v563]], %[[v561]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v564]], %[[v562]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v566:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v567:[0-9]+]] = "llvm.load"(%[[v566]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v568:[0-9]+]] = "llvm.shl"(%[[v567]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v569:[0-9]+]] = "llvm.lshr"(%[[v567]], %[[v174]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v570:[0-9]+]] = "llvm.or"(%[[v568]], %[[v569]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v571:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v570]], %[[v571]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v573:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v574:[0-9]+]] = "llvm.load"(%[[v573]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v575:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v222]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v576:[0-9]+]] = "llvm.load"(%[[v575]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v577:[0-9]+]] = "llvm.add"(%[[v576]], %[[v574]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v577]], %[[v575]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v579:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v222]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v580:[0-9]+]] = "llvm.load"(%[[v579]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v581:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v582:[0-9]+]] = "llvm.load"(%[[v581]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v583:[0-9]+]] = "llvm.xor"(%[[v582]], %[[v580]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v583]], %[[v581]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v585:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v586:[0-9]+]] = "llvm.load"(%[[v585]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v587:[0-9]+]] = "llvm.shl"(%[[v586]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v588:[0-9]+]] = "llvm.lshr"(%[[v586]], %[[v194]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v589:[0-9]+]] = "llvm.or"(%[[v587]], %[[v588]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v590:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v589]], %[[v590]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v592:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v145]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v593:[0-9]+]] = "llvm.load"(%[[v592]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v594:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v403]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v595:[0-9]+]] = "llvm.load"(%[[v594]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v596:[0-9]+]] = "llvm.add"(%[[v595]], %[[v593]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v596]], %[[v594]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v598:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v403]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v599:[0-9]+]] = "llvm.load"(%[[v598]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v600:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v601:[0-9]+]] = "llvm.load"(%[[v600]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v602:[0-9]+]] = "llvm.xor"(%[[v601]], %[[v599]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v602]], %[[v600]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v604:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v605:[0-9]+]] = "llvm.load"(%[[v604]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v606:[0-9]+]] = "llvm.shl"(%[[v605]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v607:[0-9]+]] = "llvm.lshr"(%[[v605]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v608:[0-9]+]] = "llvm.or"(%[[v606]], %[[v607]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v609:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v299]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v608]], %[[v609]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v611:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v612:[0-9]+]] = "llvm.load"(%[[v611]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v613:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v302]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v614:[0-9]+]] = "llvm.load"(%[[v613]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v615:[0-9]+]] = "llvm.add"(%[[v614]], %[[v612]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v615]], %[[v613]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v617:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v302]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v618:[0-9]+]] = "llvm.load"(%[[v617]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v619:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v620:[0-9]+]] = "llvm.load"(%[[v619]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v621:[0-9]+]] = "llvm.xor"(%[[v620]], %[[v618]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v621]], %[[v619]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v623:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v624:[0-9]+]] = "llvm.load"(%[[v623]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v625:[0-9]+]] = "llvm.shl"(%[[v624]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v626:[0-9]+]] = "llvm.lshr"(%[[v624]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v627:[0-9]+]] = "llvm.or"(%[[v625]], %[[v626]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v628:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v627]], %[[v628]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v630:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v631:[0-9]+]] = "llvm.load"(%[[v630]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v632:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v160]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v633:[0-9]+]] = "llvm.load"(%[[v632]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v634:[0-9]+]] = "llvm.add"(%[[v633]], %[[v631]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v634]], %[[v632]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v636:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v160]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v637:[0-9]+]] = "llvm.load"(%[[v636]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v638:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v639:[0-9]+]] = "llvm.load"(%[[v638]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v640:[0-9]+]] = "llvm.xor"(%[[v639]], %[[v637]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v640]], %[[v638]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v642:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v643:[0-9]+]] = "llvm.load"(%[[v642]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v644:[0-9]+]] = "llvm.shl"(%[[v643]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v645:[0-9]+]] = "llvm.lshr"(%[[v643]], %[[v174]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v646:[0-9]+]] = "llvm.or"(%[[v644]], %[[v645]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v647:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v646]], %[[v647]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v649:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v650:[0-9]+]] = "llvm.load"(%[[v649]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v651:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v302]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v652:[0-9]+]] = "llvm.load"(%[[v651]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v653:[0-9]+]] = "llvm.add"(%[[v652]], %[[v650]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v653]], %[[v651]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v655:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v302]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v656:[0-9]+]] = "llvm.load"(%[[v655]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v657:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v658:[0-9]+]] = "llvm.load"(%[[v657]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v659:[0-9]+]] = "llvm.xor"(%[[v658]], %[[v656]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v659]], %[[v657]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v661:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v662:[0-9]+]] = "llvm.load"(%[[v661]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v663:[0-9]+]] = "llvm.shl"(%[[v662]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v664:[0-9]+]] = "llvm.lshr"(%[[v662]], %[[v194]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v665:[0-9]+]] = "llvm.or"(%[[v663]], %[[v664]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v666:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v665]], %[[v666]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v668:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v229]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v669:[0-9]+]] = "llvm.load"(%[[v668]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v670:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v160]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v671:[0-9]+]] = "llvm.load"(%[[v670]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v672:[0-9]+]] = "llvm.add"(%[[v671]], %[[v669]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v672]], %[[v670]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v674:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v160]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v675:[0-9]+]] = "llvm.load"(%[[v674]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v676:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v677:[0-9]+]] = "llvm.load"(%[[v676]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v678:[0-9]+]] = "llvm.xor"(%[[v677]], %[[v675]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v678]], %[[v676]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v680:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v681:[0-9]+]] = "llvm.load"(%[[v680]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v682:[0-9]+]] = "llvm.shl"(%[[v681]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v683:[0-9]+]] = "llvm.lshr"(%[[v681]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v684:[0-9]+]] = "llvm.or"(%[[v682]], %[[v683]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v685:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v379]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v684]], %[[v685]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v687:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v688:[0-9]+]] = "llvm.load"(%[[v687]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v689:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v382]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v690:[0-9]+]] = "llvm.load"(%[[v689]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v691:[0-9]+]] = "llvm.add"(%[[v690]], %[[v688]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v691]], %[[v689]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v693:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v382]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v694:[0-9]+]] = "llvm.load"(%[[v693]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v695:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v696:[0-9]+]] = "llvm.load"(%[[v695]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v697:[0-9]+]] = "llvm.xor"(%[[v696]], %[[v694]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v697]], %[[v695]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v699:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v700:[0-9]+]] = "llvm.load"(%[[v699]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v701:[0-9]+]] = "llvm.shl"(%[[v700]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v702:[0-9]+]] = "llvm.lshr"(%[[v700]], %[[v153]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v703:[0-9]+]] = "llvm.or"(%[[v701]], %[[v702]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v704:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v703]], %[[v704]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v706:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v707:[0-9]+]] = "llvm.load"(%[[v706]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v708:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v243]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v709:[0-9]+]] = "llvm.load"(%[[v708]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v710:[0-9]+]] = "llvm.add"(%[[v709]], %[[v707]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v710]], %[[v708]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v712:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v243]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v713:[0-9]+]] = "llvm.load"(%[[v712]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v714:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v715:[0-9]+]] = "llvm.load"(%[[v714]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v716:[0-9]+]] = "llvm.xor"(%[[v715]], %[[v713]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v716]], %[[v714]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v718:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v719:[0-9]+]] = "llvm.load"(%[[v718]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v720:[0-9]+]] = "llvm.shl"(%[[v719]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v721:[0-9]+]] = "llvm.lshr"(%[[v719]], %[[v174]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v722:[0-9]+]] = "llvm.or"(%[[v720]], %[[v721]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v723:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v722]], %[[v723]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v725:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v726:[0-9]+]] = "llvm.load"(%[[v725]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v727:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v382]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v728:[0-9]+]] = "llvm.load"(%[[v727]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v729:[0-9]+]] = "llvm.add"(%[[v728]], %[[v726]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v729]], %[[v727]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v731:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v382]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v732:[0-9]+]] = "llvm.load"(%[[v731]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v733:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v734:[0-9]+]] = "llvm.load"(%[[v733]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v735:[0-9]+]] = "llvm.xor"(%[[v734]], %[[v732]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v735]], %[[v733]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v737:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v738:[0-9]+]] = "llvm.load"(%[[v737]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v739:[0-9]+]] = "llvm.shl"(%[[v738]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v740:[0-9]+]] = "llvm.lshr"(%[[v738]], %[[v194]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v741:[0-9]+]] = "llvm.or"(%[[v739]], %[[v740]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v742:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v741]], %[[v742]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v744:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v309]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v745:[0-9]+]] = "llvm.load"(%[[v744]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v746:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v243]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v747:[0-9]+]] = "llvm.load"(%[[v746]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v748:[0-9]+]] = "llvm.add"(%[[v747]], %[[v745]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v748]], %[[v746]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v750:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v243]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v751:[0-9]+]] = "llvm.load"(%[[v750]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v752:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v753:[0-9]+]] = "llvm.load"(%[[v752]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v754:[0-9]+]] = "llvm.xor"(%[[v753]], %[[v751]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v754]], %[[v752]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v756:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v757:[0-9]+]] = "llvm.load"(%[[v756]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v758:[0-9]+]] = "llvm.shl"(%[[v757]], %[[v28]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v759:[0-9]+]] = "llvm.lshr"(%[[v757]], %[[v214]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v760:[0-9]+]] = "llvm.or"(%[[v758]], %[[v759]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v761:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[v135]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v760]], %[[v761]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb763:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb763]]():
// CHECK-NEXT:         %[[v765:[0-9]+]] = "llvm.add"(%[[varg129_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v765]]) [^[[bb129]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb133]]():
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb767:[0-9]+]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb767]](%[[varg767_0:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v769:[0-9]+]] = "llvm.icmp"(%[[varg767_0]], %[[v18]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v769]]) [^[[bb770:[0-9]+]], ^[[bb771:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb770]]():
// CHECK-NEXT:         %[[v773:[0-9]+]] = "llvm.mul"(%[[v20]], %[[varg767_0]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[v774:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v773]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v775:[0-9]+]] = "llvm.getelementptr"(%[[varg7_5]], %[[varg767_0]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v776:[0-9]+]] = "llvm.load"(%[[v775]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v777:[0-9]+]] = "llvm.getelementptr"(%[[varg7_4]], %[[varg767_0]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v778:[0-9]+]] = "llvm.load"(%[[v777]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v779:[0-9]+]] = "llvm.add"(%[[v776]], %[[v778]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v780:[0-9]+]] = "llvm.trunc"(%[[v779]]) : (i32) -> i8
// CHECK-NEXT:         "llvm.store"(%[[v780]], %[[v774]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v782:[0-9]+]] = "llvm.lshr"(%[[v779]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v783:[0-9]+]] = "llvm.trunc"(%[[v782]]) : (i32) -> i8
// CHECK-NEXT:         %[[v784:[0-9]+]] = "llvm.getelementptr"(%[[v774]], %[[v10]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v783]], %[[v784]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v786:[0-9]+]] = "llvm.lshr"(%[[v779]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v787:[0-9]+]] = "llvm.trunc"(%[[v786]]) : (i32) -> i8
// CHECK-NEXT:         %[[v788:[0-9]+]] = "llvm.getelementptr"(%[[v774]], %[[v12]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v787]], %[[v788]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v790:[0-9]+]] = "llvm.lshr"(%[[v779]], %[[v23]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v791:[0-9]+]] = "llvm.trunc"(%[[v790]]) : (i32) -> i8
// CHECK-NEXT:         %[[v792:[0-9]+]] = "llvm.getelementptr"(%[[v774]], %[[v14]]) <{"elem_type" = i8, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v791]], %[[v792]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i8, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb794:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb794]]():
// CHECK-NEXT:         %[[v796:[0-9]+]] = "llvm.add"(%[[varg767_0]], %[[v10]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[v796]]) [^[[bb767]]] : (i64) -> ()
// CHECK-NEXT:       ^[[bb771]]():
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()

