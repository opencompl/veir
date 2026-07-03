// RUN: veir-opt %s -p=isel-br-riscv64,isel-riscv64,reconcile-cast | filecheck %s

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
// CHECK-NEXT:       ^[[bb7:[0-9]+]](%[[varg7_0:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg7_1:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg7_2:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg7_3:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg7_4:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg7_5:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v3465:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_1]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3462:[0-9]+]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3460:[0-9]+]] = "riscv.li"() <{"value" = 1634760805 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3461:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3460]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3458:[0-9]+]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3456:[0-9]+]] = "riscv.li"() <{"value" = 857760878 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3457:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3456]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3454:[0-9]+]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3452:[0-9]+]] = "riscv.li"() <{"value" = 2036477234 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3453:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3452]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3450:[0-9]+]] = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3448:[0-9]+]] = "riscv.li"() <{"value" = 1797285236 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3449:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3448]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3446:[0-9]+]] = "riscv.li"() <{"value" = 8 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3444:[0-9]+]] = "riscv.li"() <{"value" = 12 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3442:[0-9]+]] = "riscv.li"() <{"value" = 16 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3440:[0-9]+]] = "riscv.li"() <{"value" = 10 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3438:[0-9]+]] = "riscv.li"() <{"value" = 4 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3436:[0-9]+]] = "riscv.li"() <{"value" = 8 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3437:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3436]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3434:[0-9]+]] = "riscv.li"() <{"value" = 16 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3435:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3434]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3432:[0-9]+]] = "riscv.li"() <{"value" = 24 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3433:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3432]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3430:[0-9]+]] = "riscv.li"() <{"value" = 4 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3431:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3430]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3428:[0-9]+]] = "riscv.li"() <{"value" = 0 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3429:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3428]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3426:[0-9]+]] = "riscv.li"() <{"value" = 12 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3427:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3426]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3424:[0-9]+]] = "riscv.li"() <{"value" = 32 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3425:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3424]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3422:[0-9]+]] = "riscv.li"() <{"value" = 7 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3423:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3422]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3420:[0-9]+]] = "riscv.li"() <{"value" = 5 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3421:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3420]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3418:[0-9]+]] = "riscv.li"() <{"value" = 1 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3419:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3418]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3416:[0-9]+]] = "riscv.li"() <{"value" = 13 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3417:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3416]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3414:[0-9]+]] = "riscv.li"() <{"value" = 9 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3415:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3414]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3412:[0-9]+]] = "riscv.li"() <{"value" = 6 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3413:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3412]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3410:[0-9]+]] = "riscv.li"() <{"value" = 2 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3411:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3410]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3408:[0-9]+]] = "riscv.li"() <{"value" = 14 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3409:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3408]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3406:[0-9]+]] = "riscv.li"() <{"value" = 10 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3407:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3406]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3404:[0-9]+]] = "riscv.li"() <{"value" = 3 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3405:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3404]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3402:[0-9]+]] = "riscv.li"() <{"value" = 15 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3403:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3402]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3400:[0-9]+]] = "riscv.li"() <{"value" = 11 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3401:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3400]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3398:[0-9]+]] = "riscv.li"() <{"value" = 13 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v3396:[0-9]+]] = "riscv.sh2add"(%[[v3462]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3392:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3461]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3396]], %[[v3392]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3389:[0-9]+]] = "riscv.sh2add"(%[[v3458]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3385:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3457]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3389]], %[[v3385]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3382:[0-9]+]] = "riscv.sh2add"(%[[v3454]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3378:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3453]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3382]], %[[v3378]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3375:[0-9]+]] = "riscv.sh2add"(%[[v3450]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3371:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3449]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3375]], %[[v3371]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"(%[[v3462]]) [^[[bb49:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb49]](%[[varg49_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v3368:[0-9]+]] = "riscv.slt"(%[[varg49_0]], %[[v3446]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3369:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3368]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v827:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3369]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v827]]) [^[[bb52:[0-9]+]], ^[[bb53:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb52]]():
// CHECK-NEXT:         %[[v3364:[0-9]+]] = "riscv.mul"(%[[varg49_0]], %[[v3438]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3360:[0-9]+]] = "riscv.add"(%[[varg7_0]], %[[v3364]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3356:[0-9]+]] = "riscv.lb"(%[[v3360]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3357:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3356]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v3352:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3357]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         %[[v3353:[0-9]+]] = "riscv.zextb"(%[[v3352]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3354:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3353]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3350:[0-9]+]] = "riscv.add"(%[[v3360]], %[[v3458]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3346:[0-9]+]] = "riscv.lb"(%[[v3350]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3347:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3346]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v3342:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3347]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         %[[v3343:[0-9]+]] = "riscv.zextb"(%[[v3342]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3344:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3343]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3338:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3344]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3339:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3340:[0-9]+]] = "riscv.sllw"(%[[v3338]], %[[v3339]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3341:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3340]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3334:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3354]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3335:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3341]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3336:[0-9]+]] = "riscv.or"(%[[v3335]], %[[v3334]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3337:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3336]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3332:[0-9]+]] = "riscv.add"(%[[v3360]], %[[v3454]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3328:[0-9]+]] = "riscv.lb"(%[[v3332]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3329:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3328]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v3324:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3329]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         %[[v3325:[0-9]+]] = "riscv.zextb"(%[[v3324]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3326:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3325]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3320:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3326]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3321:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3322:[0-9]+]] = "riscv.sllw"(%[[v3320]], %[[v3321]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3323:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3322]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3316:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3337]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3317:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3323]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3318:[0-9]+]] = "riscv.or"(%[[v3317]], %[[v3316]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3319:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3318]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3314:[0-9]+]] = "riscv.add"(%[[v3360]], %[[v3450]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3310:[0-9]+]] = "riscv.lb"(%[[v3314]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3311:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3310]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v3306:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3311]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         %[[v3307:[0-9]+]] = "riscv.zextb"(%[[v3306]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3308:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3307]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3302:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3308]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3303:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3433]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3304:[0-9]+]] = "riscv.sllw"(%[[v3302]], %[[v3303]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3305:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3304]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3298:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3319]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3299:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3305]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3300:[0-9]+]] = "riscv.or"(%[[v3299]], %[[v3298]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3301:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3300]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3296:[0-9]+]] = "riscv.add"(%[[varg49_0]], %[[v3438]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3292:[0-9]+]] = "riscv.sh2add"(%[[v3296]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3288:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3301]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3292]], %[[v3288]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb77:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb77]]():
// CHECK-NEXT:         %[[v3285:[0-9]+]] = "riscv.add"(%[[v3458]], %[[varg49_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v3285]]) [^[[bb49]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb53]]():
// CHECK-NEXT:         %[[v3281:[0-9]+]] = "riscv.sh2add"(%[[v3444]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3277:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3465]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3281]], %[[v3277]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"(%[[v3462]]) [^[[bb83:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb83]](%[[varg83_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v3274:[0-9]+]] = "riscv.slt"(%[[varg83_0]], %[[v3450]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3275:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3274]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v829:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3275]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v829]]) [^[[bb86:[0-9]+]], ^[[bb87:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb86]]():
// CHECK-NEXT:         %[[v3270:[0-9]+]] = "riscv.mul"(%[[varg83_0]], %[[v3438]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3266:[0-9]+]] = "riscv.add"(%[[varg7_2]], %[[v3270]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3262:[0-9]+]] = "riscv.lb"(%[[v3266]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3263:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3262]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v3258:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3263]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         %[[v3259:[0-9]+]] = "riscv.zextb"(%[[v3258]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3260:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3259]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3256:[0-9]+]] = "riscv.add"(%[[v3266]], %[[v3458]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3252:[0-9]+]] = "riscv.lb"(%[[v3256]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3253:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3252]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v3248:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3253]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         %[[v3249:[0-9]+]] = "riscv.zextb"(%[[v3248]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3250:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3249]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3244:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3245:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3246:[0-9]+]] = "riscv.sllw"(%[[v3244]], %[[v3245]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3247:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3246]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3240:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3260]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3241:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3247]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3242:[0-9]+]] = "riscv.or"(%[[v3241]], %[[v3240]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3243:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3242]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3238:[0-9]+]] = "riscv.add"(%[[v3266]], %[[v3454]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3234:[0-9]+]] = "riscv.lb"(%[[v3238]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3235:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3234]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v3230:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3235]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         %[[v3231:[0-9]+]] = "riscv.zextb"(%[[v3230]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3232:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3231]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3226:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3232]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3227:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3228:[0-9]+]] = "riscv.sllw"(%[[v3226]], %[[v3227]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3229:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3228]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3222:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3243]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3223:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3229]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3224:[0-9]+]] = "riscv.or"(%[[v3223]], %[[v3222]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3225:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3224]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3220:[0-9]+]] = "riscv.add"(%[[v3266]], %[[v3450]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3216:[0-9]+]] = "riscv.lb"(%[[v3220]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3217:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3216]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v3212:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3217]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         %[[v3213:[0-9]+]] = "riscv.zextb"(%[[v3212]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3214:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3213]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3208:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3214]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3209:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3433]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3210:[0-9]+]] = "riscv.sllw"(%[[v3208]], %[[v3209]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3211:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3210]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3204:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3225]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3205:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3211]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3206:[0-9]+]] = "riscv.or"(%[[v3205]], %[[v3204]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3207:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3206]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3202:[0-9]+]] = "riscv.add"(%[[varg83_0]], %[[v3398]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3198:[0-9]+]] = "riscv.sh2add"(%[[v3202]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3194:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3207]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3198]], %[[v3194]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb111:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb111]]():
// CHECK-NEXT:         %[[v3191:[0-9]+]] = "riscv.add"(%[[v3458]], %[[varg83_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v3191]]) [^[[bb83]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb87]]():
// CHECK-NEXT:         "riscv_cf.branch"(%[[v3462]]) [^[[bb115:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb115]](%[[varg115_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v3187:[0-9]+]] = "riscv.slt"(%[[varg115_0]], %[[v3442]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3188:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3187]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v831:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3188]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v831]]) [^[[bb118:[0-9]+]], ^[[bb119:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb118]]():
// CHECK-NEXT:         %[[v3183:[0-9]+]] = "riscv.sh2add"(%[[varg115_0]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3179:[0-9]+]] = "riscv.lw"(%[[v3183]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3180:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3179]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3176:[0-9]+]] = "riscv.sh2add"(%[[varg115_0]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3172:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3180]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3176]], %[[v3172]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb125:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb125]]():
// CHECK-NEXT:         %[[v3169:[0-9]+]] = "riscv.add"(%[[v3458]], %[[varg115_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v3169]]) [^[[bb115]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb119]]():
// CHECK-NEXT:         "riscv_cf.branch"(%[[v3462]]) [^[[bb129:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb129]](%[[varg129_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v3165:[0-9]+]] = "riscv.slt"(%[[varg129_0]], %[[v3440]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3166:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3165]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v808:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3166]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v808]]) [^[[bb132:[0-9]+]], ^[[bb133:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb132]]():
// CHECK-NEXT:         %[[v3160:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3431]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3161:[0-9]+]] = "riscv.sextw"(%[[v3160]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3158:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3154:[0-9]+]] = "riscv.lw"(%[[v3158]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3155:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3154]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3150:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3429]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3151:[0-9]+]] = "riscv.sextw"(%[[v3150]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3148:[0-9]+]] = "riscv.sh2add"(%[[v3151]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3144:[0-9]+]] = "riscv.lw"(%[[v3148]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3145:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3144]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3139:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3145]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3140:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3155]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3141:[0-9]+]] = "riscv.addw"(%[[v3140]], %[[v3139]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3142:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3141]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3137:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3142]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3148]], %[[v3137]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3134:[0-9]+]] = "riscv.sh2add"(%[[v3151]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3130:[0-9]+]] = "riscv.lw"(%[[v3134]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3131:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3130]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3126:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3127:[0-9]+]] = "riscv.sextw"(%[[v3126]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3124:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3120:[0-9]+]] = "riscv.lw"(%[[v3124]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3121:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3120]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3115:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3121]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3116:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3131]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3117:[0-9]+]] = "riscv.xor"(%[[v3116]], %[[v3115]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3118:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3117]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3113:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3118]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3124]], %[[v3113]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3110:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3106:[0-9]+]] = "riscv.lw"(%[[v3110]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3107:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3106]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3101:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3107]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3102:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3103:[0-9]+]] = "riscv.sllw"(%[[v3101]], %[[v3102]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3104:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3103]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3097:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3425]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3098:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3099:[0-9]+]] = "riscv.subw"(%[[v3097]], %[[v3098]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3100:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3099]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3093:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3107]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3094:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3095:[0-9]+]] = "riscv.srlw"(%[[v3093]], %[[v3094]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3096:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3095]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3089:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3104]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3090:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3096]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3091:[0-9]+]] = "riscv.or"(%[[v3090]], %[[v3089]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3092:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3091]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3087:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3083:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3092]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3087]], %[[v3083]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3080:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3076:[0-9]+]] = "riscv.lw"(%[[v3080]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3077:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3076]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3072:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3073:[0-9]+]] = "riscv.sextw"(%[[v3072]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3070:[0-9]+]] = "riscv.sh2add"(%[[v3073]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3066:[0-9]+]] = "riscv.lw"(%[[v3070]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3067:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3066]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3061:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3067]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3062:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3077]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3063:[0-9]+]] = "riscv.addw"(%[[v3062]], %[[v3061]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3064:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3063]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3059:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3064]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3070]], %[[v3059]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3056:[0-9]+]] = "riscv.sh2add"(%[[v3073]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3052:[0-9]+]] = "riscv.lw"(%[[v3056]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3053:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3052]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3049:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3045:[0-9]+]] = "riscv.lw"(%[[v3049]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3046:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3045]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3040:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3046]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3041:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3053]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3042:[0-9]+]] = "riscv.xor"(%[[v3041]], %[[v3040]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3043:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3042]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3038:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3043]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3049]], %[[v3038]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3035:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3031:[0-9]+]] = "riscv.lw"(%[[v3035]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3032:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3031]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3026:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3032]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3027:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3028:[0-9]+]] = "riscv.sllw"(%[[v3026]], %[[v3027]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3029:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3028]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3022:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3425]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3023:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3024:[0-9]+]] = "riscv.subw"(%[[v3022]], %[[v3023]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3025:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3024]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3018:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3032]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3019:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3020:[0-9]+]] = "riscv.srlw"(%[[v3018]], %[[v3019]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3021:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3020]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3014:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3029]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3015:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3021]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v3016:[0-9]+]] = "riscv.or"(%[[v3015]], %[[v3014]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3017:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3016]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v3012:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3008:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3017]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v3012]], %[[v3008]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v3005:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3001:[0-9]+]] = "riscv.lw"(%[[v3005]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v3002:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3001]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2998:[0-9]+]] = "riscv.sh2add"(%[[v3151]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2994:[0-9]+]] = "riscv.lw"(%[[v2998]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2995:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2994]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2989:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2995]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2990:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3002]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2991:[0-9]+]] = "riscv.addw"(%[[v2990]], %[[v2989]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2992:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2991]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2987:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2992]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2998]], %[[v2987]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2984:[0-9]+]] = "riscv.sh2add"(%[[v3151]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2980:[0-9]+]] = "riscv.lw"(%[[v2984]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2981:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2980]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2977:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2973:[0-9]+]] = "riscv.lw"(%[[v2977]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2974:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2973]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2968:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2974]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2969:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2981]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2970:[0-9]+]] = "riscv.xor"(%[[v2969]], %[[v2968]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2971:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2970]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2966:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2971]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2977]], %[[v2966]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2963:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2959:[0-9]+]] = "riscv.lw"(%[[v2963]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2960:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2959]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2954:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2960]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2955:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2956:[0-9]+]] = "riscv.sllw"(%[[v2954]], %[[v2955]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2957:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2956]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2950:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3425]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2951:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2952:[0-9]+]] = "riscv.subw"(%[[v2950]], %[[v2951]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2953:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2952]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2946:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2960]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2947:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2948:[0-9]+]] = "riscv.srlw"(%[[v2946]], %[[v2947]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2949:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2948]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2942:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2957]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2943:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2949]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2944:[0-9]+]] = "riscv.or"(%[[v2943]], %[[v2942]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2945:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2944]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2940:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2936:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2945]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2940]], %[[v2936]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2933:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2929:[0-9]+]] = "riscv.lw"(%[[v2933]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2930:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2929]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2926:[0-9]+]] = "riscv.sh2add"(%[[v3073]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2922:[0-9]+]] = "riscv.lw"(%[[v2926]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2923:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2922]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2917:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2923]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2918:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2930]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2919:[0-9]+]] = "riscv.addw"(%[[v2918]], %[[v2917]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2920:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2919]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2915:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2920]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2926]], %[[v2915]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2912:[0-9]+]] = "riscv.sh2add"(%[[v3073]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2908:[0-9]+]] = "riscv.lw"(%[[v2912]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2909:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2908]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2905:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2901:[0-9]+]] = "riscv.lw"(%[[v2905]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2902:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2901]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2896:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2902]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2897:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2909]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2898:[0-9]+]] = "riscv.xor"(%[[v2897]], %[[v2896]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2899:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2898]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2894:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2899]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2905]], %[[v2894]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2891:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2887:[0-9]+]] = "riscv.lw"(%[[v2891]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2888:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2887]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2882:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2888]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2883:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2884:[0-9]+]] = "riscv.sllw"(%[[v2882]], %[[v2883]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2885:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2884]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2878:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3425]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2879:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2880:[0-9]+]] = "riscv.subw"(%[[v2878]], %[[v2879]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2881:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2880]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2874:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2888]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2875:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2876:[0-9]+]] = "riscv.srlw"(%[[v2874]], %[[v2875]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2877:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2876]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2870:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2885]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2871:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2877]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2872:[0-9]+]] = "riscv.or"(%[[v2871]], %[[v2870]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2873:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2872]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2868:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2864:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2873]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2868]], %[[v2864]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2860:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3421]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2861:[0-9]+]] = "riscv.sextw"(%[[v2860]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2858:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2854:[0-9]+]] = "riscv.lw"(%[[v2858]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2855:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2854]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2850:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3419]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2851:[0-9]+]] = "riscv.sextw"(%[[v2850]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2848:[0-9]+]] = "riscv.sh2add"(%[[v2851]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2844:[0-9]+]] = "riscv.lw"(%[[v2848]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2845:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2844]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2839:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2845]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2840:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2855]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2841:[0-9]+]] = "riscv.addw"(%[[v2840]], %[[v2839]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2842:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2841]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2837:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2842]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2848]], %[[v2837]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2834:[0-9]+]] = "riscv.sh2add"(%[[v2851]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2830:[0-9]+]] = "riscv.lw"(%[[v2834]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2831:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2830]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2826:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3417]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2827:[0-9]+]] = "riscv.sextw"(%[[v2826]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2824:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2820:[0-9]+]] = "riscv.lw"(%[[v2824]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2821:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2820]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2815:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2821]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2816:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2831]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2817:[0-9]+]] = "riscv.xor"(%[[v2816]], %[[v2815]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2818:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2817]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2813:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2818]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2824]], %[[v2813]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2810:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2806:[0-9]+]] = "riscv.lw"(%[[v2810]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2807:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2806]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2801:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2807]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2802:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2803:[0-9]+]] = "riscv.sllw"(%[[v2801]], %[[v2802]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2804:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2803]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2797:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2807]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2798:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2799:[0-9]+]] = "riscv.srlw"(%[[v2797]], %[[v2798]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2800:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2799]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2793:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2804]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2794:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2800]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2795:[0-9]+]] = "riscv.or"(%[[v2794]], %[[v2793]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2796:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2795]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2791:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2787:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2796]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2791]], %[[v2787]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2784:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2780:[0-9]+]] = "riscv.lw"(%[[v2784]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2781:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2780]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2776:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3415]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2777:[0-9]+]] = "riscv.sextw"(%[[v2776]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2774:[0-9]+]] = "riscv.sh2add"(%[[v2777]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2770:[0-9]+]] = "riscv.lw"(%[[v2774]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2771:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2770]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2765:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2771]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2766:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2781]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2767:[0-9]+]] = "riscv.addw"(%[[v2766]], %[[v2765]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2768:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2767]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2763:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2768]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2774]], %[[v2763]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2760:[0-9]+]] = "riscv.sh2add"(%[[v2777]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2756:[0-9]+]] = "riscv.lw"(%[[v2760]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2757:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2756]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2753:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2749:[0-9]+]] = "riscv.lw"(%[[v2753]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2750:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2749]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2744:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2750]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2745:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2757]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2746:[0-9]+]] = "riscv.xor"(%[[v2745]], %[[v2744]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2747:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2746]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2742:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2747]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2753]], %[[v2742]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2739:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2735:[0-9]+]] = "riscv.lw"(%[[v2739]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2736:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2735]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2730:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2736]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2731:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2732:[0-9]+]] = "riscv.sllw"(%[[v2730]], %[[v2731]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2733:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2732]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2726:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2736]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2727:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2728:[0-9]+]] = "riscv.srlw"(%[[v2726]], %[[v2727]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2729:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2728]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2722:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2733]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2723:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2729]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2724:[0-9]+]] = "riscv.or"(%[[v2723]], %[[v2722]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2725:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2724]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2720:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2716:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2725]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2720]], %[[v2716]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2713:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2709:[0-9]+]] = "riscv.lw"(%[[v2713]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2710:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2709]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2706:[0-9]+]] = "riscv.sh2add"(%[[v2851]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2702:[0-9]+]] = "riscv.lw"(%[[v2706]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2703:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2702]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2697:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2703]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2698:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2710]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2699:[0-9]+]] = "riscv.addw"(%[[v2698]], %[[v2697]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2700:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2699]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2695:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2700]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2706]], %[[v2695]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2692:[0-9]+]] = "riscv.sh2add"(%[[v2851]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2688:[0-9]+]] = "riscv.lw"(%[[v2692]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2689:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2688]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2685:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2681:[0-9]+]] = "riscv.lw"(%[[v2685]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2682:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2681]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2676:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2682]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2677:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2689]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2678:[0-9]+]] = "riscv.xor"(%[[v2677]], %[[v2676]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2679:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2678]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2674:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2679]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2685]], %[[v2674]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2671:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2667:[0-9]+]] = "riscv.lw"(%[[v2671]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2668:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2667]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2662:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2668]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2663:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2664:[0-9]+]] = "riscv.sllw"(%[[v2662]], %[[v2663]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2665:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2664]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2658:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2668]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2659:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2660:[0-9]+]] = "riscv.srlw"(%[[v2658]], %[[v2659]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2661:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2660]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2654:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2665]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2655:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2661]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2656:[0-9]+]] = "riscv.or"(%[[v2655]], %[[v2654]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2657:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2656]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2652:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2648:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2657]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2652]], %[[v2648]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2645:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2641:[0-9]+]] = "riscv.lw"(%[[v2645]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2642:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2641]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2638:[0-9]+]] = "riscv.sh2add"(%[[v2777]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2634:[0-9]+]] = "riscv.lw"(%[[v2638]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2635:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2634]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2629:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2635]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2630:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2642]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2631:[0-9]+]] = "riscv.addw"(%[[v2630]], %[[v2629]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2632:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2631]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2627:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2632]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2638]], %[[v2627]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2624:[0-9]+]] = "riscv.sh2add"(%[[v2777]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2620:[0-9]+]] = "riscv.lw"(%[[v2624]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2621:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2620]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2617:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2613:[0-9]+]] = "riscv.lw"(%[[v2617]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2614:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2613]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2608:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2614]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2609:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2621]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2610:[0-9]+]] = "riscv.xor"(%[[v2609]], %[[v2608]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2611:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2610]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2606:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2611]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2617]], %[[v2606]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2603:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2599:[0-9]+]] = "riscv.lw"(%[[v2603]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2600:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2599]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2594:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2600]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2595:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2596:[0-9]+]] = "riscv.sllw"(%[[v2594]], %[[v2595]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2597:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2596]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2590:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2600]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2591:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2592:[0-9]+]] = "riscv.srlw"(%[[v2590]], %[[v2591]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2593:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2592]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2586:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2597]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2587:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2593]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2588:[0-9]+]] = "riscv.or"(%[[v2587]], %[[v2586]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2589:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2588]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2584:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2580:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2589]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2584]], %[[v2580]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2576:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3413]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2577:[0-9]+]] = "riscv.sextw"(%[[v2576]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2574:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2570:[0-9]+]] = "riscv.lw"(%[[v2574]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2571:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2570]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2566:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3411]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2567:[0-9]+]] = "riscv.sextw"(%[[v2566]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2564:[0-9]+]] = "riscv.sh2add"(%[[v2567]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2560:[0-9]+]] = "riscv.lw"(%[[v2564]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2561:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2560]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2555:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2561]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2556:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2571]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2557:[0-9]+]] = "riscv.addw"(%[[v2556]], %[[v2555]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2558:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2557]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2553:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2558]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2564]], %[[v2553]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2550:[0-9]+]] = "riscv.sh2add"(%[[v2567]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2546:[0-9]+]] = "riscv.lw"(%[[v2550]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2547:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2546]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2542:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3409]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2543:[0-9]+]] = "riscv.sextw"(%[[v2542]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2540:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2536:[0-9]+]] = "riscv.lw"(%[[v2540]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2537:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2536]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2531:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2537]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2532:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2547]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2533:[0-9]+]] = "riscv.xor"(%[[v2532]], %[[v2531]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2534:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2533]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2529:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2534]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2540]], %[[v2529]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2526:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2522:[0-9]+]] = "riscv.lw"(%[[v2526]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2523:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2522]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2517:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2523]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2518:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2519:[0-9]+]] = "riscv.sllw"(%[[v2517]], %[[v2518]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2520:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2519]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2513:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2523]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2514:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2515:[0-9]+]] = "riscv.srlw"(%[[v2513]], %[[v2514]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2516:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2515]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2509:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2520]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2510:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2516]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2511:[0-9]+]] = "riscv.or"(%[[v2510]], %[[v2509]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2512:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2511]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2507:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2503:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2512]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2507]], %[[v2503]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2500:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2496:[0-9]+]] = "riscv.lw"(%[[v2500]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2497:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2496]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2492:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3407]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2493:[0-9]+]] = "riscv.sextw"(%[[v2492]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2490:[0-9]+]] = "riscv.sh2add"(%[[v2493]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2486:[0-9]+]] = "riscv.lw"(%[[v2490]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2487:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2486]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2481:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2487]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2482:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2497]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2483:[0-9]+]] = "riscv.addw"(%[[v2482]], %[[v2481]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2484:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2483]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2479:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2484]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2490]], %[[v2479]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2476:[0-9]+]] = "riscv.sh2add"(%[[v2493]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2472:[0-9]+]] = "riscv.lw"(%[[v2476]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2473:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2472]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2469:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2465:[0-9]+]] = "riscv.lw"(%[[v2469]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2466:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2465]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2460:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2466]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2461:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2473]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2462:[0-9]+]] = "riscv.xor"(%[[v2461]], %[[v2460]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2463:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2462]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2458:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2463]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2469]], %[[v2458]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2455:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2451:[0-9]+]] = "riscv.lw"(%[[v2455]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2452:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2451]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2446:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2452]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2447:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2448:[0-9]+]] = "riscv.sllw"(%[[v2446]], %[[v2447]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2449:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2448]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2442:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2452]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2443:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2444:[0-9]+]] = "riscv.srlw"(%[[v2442]], %[[v2443]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2445:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2444]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2438:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2449]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2439:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2445]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2440:[0-9]+]] = "riscv.or"(%[[v2439]], %[[v2438]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2441:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2440]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2436:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2432:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2441]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2436]], %[[v2432]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2429:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2425:[0-9]+]] = "riscv.lw"(%[[v2429]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2426:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2425]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2422:[0-9]+]] = "riscv.sh2add"(%[[v2567]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2418:[0-9]+]] = "riscv.lw"(%[[v2422]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2419:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2418]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2413:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2419]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2414:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2426]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2415:[0-9]+]] = "riscv.addw"(%[[v2414]], %[[v2413]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2416:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2415]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2411:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2416]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2422]], %[[v2411]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2408:[0-9]+]] = "riscv.sh2add"(%[[v2567]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2404:[0-9]+]] = "riscv.lw"(%[[v2408]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2405:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2404]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2401:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2397:[0-9]+]] = "riscv.lw"(%[[v2401]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2398:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2397]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2392:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2398]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2393:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2405]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2394:[0-9]+]] = "riscv.xor"(%[[v2393]], %[[v2392]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2395:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2394]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2390:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2395]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2401]], %[[v2390]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2387:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2383:[0-9]+]] = "riscv.lw"(%[[v2387]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2384:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2383]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2378:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2384]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2379:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2380:[0-9]+]] = "riscv.sllw"(%[[v2378]], %[[v2379]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2381:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2380]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2374:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2384]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2375:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2376:[0-9]+]] = "riscv.srlw"(%[[v2374]], %[[v2375]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2377:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2376]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2370:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2381]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2371:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2377]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2372:[0-9]+]] = "riscv.or"(%[[v2371]], %[[v2370]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2373:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2372]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2368:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2364:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2373]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2368]], %[[v2364]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2361:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2357:[0-9]+]] = "riscv.lw"(%[[v2361]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2358:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2357]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2354:[0-9]+]] = "riscv.sh2add"(%[[v2493]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2350:[0-9]+]] = "riscv.lw"(%[[v2354]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2351:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2350]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2345:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2351]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2346:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2358]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2347:[0-9]+]] = "riscv.addw"(%[[v2346]], %[[v2345]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2348:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2347]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2343:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2348]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2354]], %[[v2343]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2340:[0-9]+]] = "riscv.sh2add"(%[[v2493]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2336:[0-9]+]] = "riscv.lw"(%[[v2340]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2337:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2336]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2333:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2329:[0-9]+]] = "riscv.lw"(%[[v2333]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2330:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2329]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2324:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2330]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2325:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2337]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2326:[0-9]+]] = "riscv.xor"(%[[v2325]], %[[v2324]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2327:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2326]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2322:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2327]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2333]], %[[v2322]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2319:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2315:[0-9]+]] = "riscv.lw"(%[[v2319]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2316:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2315]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2310:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2316]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2311:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2312:[0-9]+]] = "riscv.sllw"(%[[v2310]], %[[v2311]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2313:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2312]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2306:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2316]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2307:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2308:[0-9]+]] = "riscv.srlw"(%[[v2306]], %[[v2307]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2309:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2308]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2302:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2313]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2303:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2309]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2304:[0-9]+]] = "riscv.or"(%[[v2303]], %[[v2302]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2305:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2304]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2300:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2296:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2305]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2300]], %[[v2296]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2292:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2293:[0-9]+]] = "riscv.sextw"(%[[v2292]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2290:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2286:[0-9]+]] = "riscv.lw"(%[[v2290]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2287:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2286]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2282:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3405]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2283:[0-9]+]] = "riscv.sextw"(%[[v2282]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2280:[0-9]+]] = "riscv.sh2add"(%[[v2283]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2276:[0-9]+]] = "riscv.lw"(%[[v2280]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2277:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2276]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2271:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2277]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2272:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2287]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2273:[0-9]+]] = "riscv.addw"(%[[v2272]], %[[v2271]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2274:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2273]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2269:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2274]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2280]], %[[v2269]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2266:[0-9]+]] = "riscv.sh2add"(%[[v2283]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2262:[0-9]+]] = "riscv.lw"(%[[v2266]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2263:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2262]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2258:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3403]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2259:[0-9]+]] = "riscv.sextw"(%[[v2258]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2256:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2252:[0-9]+]] = "riscv.lw"(%[[v2256]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2253:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2252]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2247:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2253]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2248:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2263]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2249:[0-9]+]] = "riscv.xor"(%[[v2248]], %[[v2247]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2250:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2249]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2245:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2256]], %[[v2245]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2242:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2238:[0-9]+]] = "riscv.lw"(%[[v2242]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2239:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2238]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2233:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2239]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2234:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2235:[0-9]+]] = "riscv.sllw"(%[[v2233]], %[[v2234]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2236:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2235]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2229:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2239]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2230:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2231:[0-9]+]] = "riscv.srlw"(%[[v2229]], %[[v2230]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2232:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2231]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2225:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2236]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2226:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2232]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2227:[0-9]+]] = "riscv.or"(%[[v2226]], %[[v2225]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2228:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2227]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2223:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2219:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2228]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2223]], %[[v2219]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2216:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2212:[0-9]+]] = "riscv.lw"(%[[v2216]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2213:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2212]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2208:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3401]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2209:[0-9]+]] = "riscv.sextw"(%[[v2208]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2206:[0-9]+]] = "riscv.sh2add"(%[[v2209]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2202:[0-9]+]] = "riscv.lw"(%[[v2206]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2203:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2202]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2197:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2203]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2198:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2213]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2199:[0-9]+]] = "riscv.addw"(%[[v2198]], %[[v2197]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2200:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2199]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2195:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2200]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2206]], %[[v2195]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2192:[0-9]+]] = "riscv.sh2add"(%[[v2209]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2188:[0-9]+]] = "riscv.lw"(%[[v2192]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2189:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2188]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2185:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2181:[0-9]+]] = "riscv.lw"(%[[v2185]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2182:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2181]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2176:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2182]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2177:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2189]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2178:[0-9]+]] = "riscv.xor"(%[[v2177]], %[[v2176]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2179:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2178]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2174:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2179]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2185]], %[[v2174]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2171:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2167:[0-9]+]] = "riscv.lw"(%[[v2171]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2168:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2167]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2162:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2168]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2163:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2164:[0-9]+]] = "riscv.sllw"(%[[v2162]], %[[v2163]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2165:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2164]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2158:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2168]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2159:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2160:[0-9]+]] = "riscv.srlw"(%[[v2158]], %[[v2159]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2161:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2160]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2154:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2165]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2155:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2161]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2156:[0-9]+]] = "riscv.or"(%[[v2155]], %[[v2154]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2157:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2156]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2152:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2148:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2157]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2152]], %[[v2148]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2145:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2141:[0-9]+]] = "riscv.lw"(%[[v2145]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2142:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2141]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2138:[0-9]+]] = "riscv.sh2add"(%[[v2283]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2134:[0-9]+]] = "riscv.lw"(%[[v2138]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2135:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2134]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2129:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2135]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2130:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2142]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2131:[0-9]+]] = "riscv.addw"(%[[v2130]], %[[v2129]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2132:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2131]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2127:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2132]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2138]], %[[v2127]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2124:[0-9]+]] = "riscv.sh2add"(%[[v2283]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2120:[0-9]+]] = "riscv.lw"(%[[v2124]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2121:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2120]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2117:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2113:[0-9]+]] = "riscv.lw"(%[[v2117]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2114:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2113]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2108:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2114]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2109:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2121]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2110:[0-9]+]] = "riscv.xor"(%[[v2109]], %[[v2108]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2111:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2110]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2106:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2111]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2117]], %[[v2106]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2103:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2099:[0-9]+]] = "riscv.lw"(%[[v2103]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2100:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2099]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2094:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2095:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2096:[0-9]+]] = "riscv.sllw"(%[[v2094]], %[[v2095]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2097:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2096]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2090:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2091:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2092:[0-9]+]] = "riscv.srlw"(%[[v2090]], %[[v2091]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2093:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2092]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2086:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2097]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2087:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2093]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2088:[0-9]+]] = "riscv.or"(%[[v2087]], %[[v2086]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2089:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2088]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2084:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2080:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2089]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2084]], %[[v2080]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2077:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2073:[0-9]+]] = "riscv.lw"(%[[v2077]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2074:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2073]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2070:[0-9]+]] = "riscv.sh2add"(%[[v2209]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2066:[0-9]+]] = "riscv.lw"(%[[v2070]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2067:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2066]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2061:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2067]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2062:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2074]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2063:[0-9]+]] = "riscv.addw"(%[[v2062]], %[[v2061]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2064:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2063]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2059:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2064]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2070]], %[[v2059]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2056:[0-9]+]] = "riscv.sh2add"(%[[v2209]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2052:[0-9]+]] = "riscv.lw"(%[[v2056]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2053:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2052]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2049:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2045:[0-9]+]] = "riscv.lw"(%[[v2049]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2046:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2045]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2040:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2046]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2041:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2053]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2042:[0-9]+]] = "riscv.xor"(%[[v2041]], %[[v2040]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2043:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2042]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2038:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2043]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2049]], %[[v2038]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2035:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2031:[0-9]+]] = "riscv.lw"(%[[v2035]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2032:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2031]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2026:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2032]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2027:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2028:[0-9]+]] = "riscv.sllw"(%[[v2026]], %[[v2027]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2029:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2028]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2022:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2032]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2023:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2024:[0-9]+]] = "riscv.srlw"(%[[v2022]], %[[v2023]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2025:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2024]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2018:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2029]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2019:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v2020:[0-9]+]] = "riscv.or"(%[[v2019]], %[[v2018]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2021:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2020]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2016:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2012:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2021]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2016]], %[[v2012]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v2009:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2005:[0-9]+]] = "riscv.lw"(%[[v2009]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v2006:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2005]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v2002:[0-9]+]] = "riscv.sh2add"(%[[v3151]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1998:[0-9]+]] = "riscv.lw"(%[[v2002]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1999:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1998]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1993:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1999]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1994:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2006]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1995:[0-9]+]] = "riscv.addw"(%[[v1994]], %[[v1993]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1996:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1995]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1991:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1996]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v2002]], %[[v1991]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1988:[0-9]+]] = "riscv.sh2add"(%[[v3151]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1984:[0-9]+]] = "riscv.lw"(%[[v1988]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1985:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1984]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1981:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1977:[0-9]+]] = "riscv.lw"(%[[v1981]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1978:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1977]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1972:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1978]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1973:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1985]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1974:[0-9]+]] = "riscv.xor"(%[[v1973]], %[[v1972]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1975:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1974]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1970:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1975]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1981]], %[[v1970]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1967:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1963:[0-9]+]] = "riscv.lw"(%[[v1967]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1964:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1963]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1958:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1964]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1959:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1960:[0-9]+]] = "riscv.sllw"(%[[v1958]], %[[v1959]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1961:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1960]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1954:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1964]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1955:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1956:[0-9]+]] = "riscv.srlw"(%[[v1954]], %[[v1955]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1957:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1956]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1950:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1961]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1951:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1957]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1952:[0-9]+]] = "riscv.or"(%[[v1951]], %[[v1950]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1953:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1952]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1948:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1944:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1948]], %[[v1944]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1941:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1937:[0-9]+]] = "riscv.lw"(%[[v1941]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1938:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1937]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1934:[0-9]+]] = "riscv.sh2add"(%[[v2493]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1930:[0-9]+]] = "riscv.lw"(%[[v1934]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1931:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1930]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1925:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1931]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1926:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1938]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1927:[0-9]+]] = "riscv.addw"(%[[v1926]], %[[v1925]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1928:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1927]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1923:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1928]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1934]], %[[v1923]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1920:[0-9]+]] = "riscv.sh2add"(%[[v2493]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1916:[0-9]+]] = "riscv.lw"(%[[v1920]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1917:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1916]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1913:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1909:[0-9]+]] = "riscv.lw"(%[[v1913]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1910:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1909]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1904:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1910]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1905:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1917]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1906:[0-9]+]] = "riscv.xor"(%[[v1905]], %[[v1904]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1907:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1906]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1902:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1907]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1913]], %[[v1902]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1899:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1895:[0-9]+]] = "riscv.lw"(%[[v1899]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1896:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1895]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1890:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1896]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1891:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1892:[0-9]+]] = "riscv.sllw"(%[[v1890]], %[[v1891]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1893:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1892]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1886:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1896]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1887:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1888:[0-9]+]] = "riscv.srlw"(%[[v1886]], %[[v1887]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1889:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1888]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1882:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1893]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1883:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1889]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1884:[0-9]+]] = "riscv.or"(%[[v1883]], %[[v1882]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1885:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1884]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1880:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1876:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1885]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1880]], %[[v1876]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1873:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1869:[0-9]+]] = "riscv.lw"(%[[v1873]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1870:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1869]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1866:[0-9]+]] = "riscv.sh2add"(%[[v3151]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1862:[0-9]+]] = "riscv.lw"(%[[v1866]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1863:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1862]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1857:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1863]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1858:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1870]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1859:[0-9]+]] = "riscv.addw"(%[[v1858]], %[[v1857]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1860:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1859]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1855:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1860]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1866]], %[[v1855]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1852:[0-9]+]] = "riscv.sh2add"(%[[v3151]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1848:[0-9]+]] = "riscv.lw"(%[[v1852]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1849:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1848]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1845:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1841:[0-9]+]] = "riscv.lw"(%[[v1845]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1842:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1841]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1836:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1842]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1837:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1849]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1838:[0-9]+]] = "riscv.xor"(%[[v1837]], %[[v1836]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1839:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1838]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1834:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1839]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1845]], %[[v1834]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1831:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1827:[0-9]+]] = "riscv.lw"(%[[v1831]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1828:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1827]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1822:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1828]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1823:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1824:[0-9]+]] = "riscv.sllw"(%[[v1822]], %[[v1823]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1825:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1824]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1818:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1828]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1819:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1820:[0-9]+]] = "riscv.srlw"(%[[v1818]], %[[v1819]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1821:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1820]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1814:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1825]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1815:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1821]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1816:[0-9]+]] = "riscv.or"(%[[v1815]], %[[v1814]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1817:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1816]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1812:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1808:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1817]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1812]], %[[v1808]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1805:[0-9]+]] = "riscv.sh2add"(%[[v2259]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1801:[0-9]+]] = "riscv.lw"(%[[v1805]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1802:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1801]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1798:[0-9]+]] = "riscv.sh2add"(%[[v2493]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1794:[0-9]+]] = "riscv.lw"(%[[v1798]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1795:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1794]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1789:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1795]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1790:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1802]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1791:[0-9]+]] = "riscv.addw"(%[[v1790]], %[[v1789]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1792:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1791]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1787:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1792]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1798]], %[[v1787]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1784:[0-9]+]] = "riscv.sh2add"(%[[v2493]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1780:[0-9]+]] = "riscv.lw"(%[[v1784]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1781:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1780]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1777:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1773:[0-9]+]] = "riscv.lw"(%[[v1777]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1774:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1773]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1768:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1774]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1769:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1781]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1770:[0-9]+]] = "riscv.xor"(%[[v1769]], %[[v1768]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1771:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1770]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1766:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1771]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1777]], %[[v1766]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1763:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1759:[0-9]+]] = "riscv.lw"(%[[v1763]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1760:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1759]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1754:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1760]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1755:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1756:[0-9]+]] = "riscv.sllw"(%[[v1754]], %[[v1755]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1757:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1756]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1750:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1760]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1751:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1752:[0-9]+]] = "riscv.srlw"(%[[v1750]], %[[v1751]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1753:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1752]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1746:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1757]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1747:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1753]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1748:[0-9]+]] = "riscv.or"(%[[v1747]], %[[v1746]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1749:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1748]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1744:[0-9]+]] = "riscv.sh2add"(%[[v2861]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1740:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1749]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1744]], %[[v1740]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1737:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1733:[0-9]+]] = "riscv.lw"(%[[v1737]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1734:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1733]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1730:[0-9]+]] = "riscv.sh2add"(%[[v2851]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1726:[0-9]+]] = "riscv.lw"(%[[v1730]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1727:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1726]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1721:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1727]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1722:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1734]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1723:[0-9]+]] = "riscv.addw"(%[[v1722]], %[[v1721]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1724:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1723]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1719:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1724]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1730]], %[[v1719]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1716:[0-9]+]] = "riscv.sh2add"(%[[v2851]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1712:[0-9]+]] = "riscv.lw"(%[[v1716]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1713:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1712]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1709:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1705:[0-9]+]] = "riscv.lw"(%[[v1709]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1706:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1705]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1700:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1706]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1701:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1713]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1702:[0-9]+]] = "riscv.xor"(%[[v1701]], %[[v1700]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1703:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1702]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1698:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1703]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1709]], %[[v1698]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1695:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1691:[0-9]+]] = "riscv.lw"(%[[v1695]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1692:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1691]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1686:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1692]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1687:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1688:[0-9]+]] = "riscv.sllw"(%[[v1686]], %[[v1687]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1689:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1688]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1682:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1692]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1683:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1684:[0-9]+]] = "riscv.srlw"(%[[v1682]], %[[v1683]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1685:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1684]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1678:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1689]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1679:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1685]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1680:[0-9]+]] = "riscv.or"(%[[v1679]], %[[v1678]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1681:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1680]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1676:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1672:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1681]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1676]], %[[v1672]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1669:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1665:[0-9]+]] = "riscv.lw"(%[[v1669]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1666:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1665]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1662:[0-9]+]] = "riscv.sh2add"(%[[v2209]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1658:[0-9]+]] = "riscv.lw"(%[[v1662]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1659:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1658]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1653:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1659]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1654:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1666]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1655:[0-9]+]] = "riscv.addw"(%[[v1654]], %[[v1653]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1656:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1655]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1651:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1656]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1662]], %[[v1651]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1648:[0-9]+]] = "riscv.sh2add"(%[[v2209]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1644:[0-9]+]] = "riscv.lw"(%[[v1648]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1645:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1644]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1641:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1637:[0-9]+]] = "riscv.lw"(%[[v1641]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1638:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1637]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1632:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1638]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1633:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1645]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1634:[0-9]+]] = "riscv.xor"(%[[v1633]], %[[v1632]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1635:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1634]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1630:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1635]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1641]], %[[v1630]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1627:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1623:[0-9]+]] = "riscv.lw"(%[[v1627]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1624:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1623]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1618:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1624]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1619:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1620:[0-9]+]] = "riscv.sllw"(%[[v1618]], %[[v1619]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1621:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1620]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1614:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1624]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1615:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1616:[0-9]+]] = "riscv.srlw"(%[[v1614]], %[[v1615]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1617:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1616]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1610:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1621]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1611:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1617]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1612:[0-9]+]] = "riscv.or"(%[[v1611]], %[[v1610]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1613:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1612]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1608:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1604:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1613]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1608]], %[[v1604]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1601:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1597:[0-9]+]] = "riscv.lw"(%[[v1601]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1598:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1597]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1594:[0-9]+]] = "riscv.sh2add"(%[[v2851]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1590:[0-9]+]] = "riscv.lw"(%[[v1594]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1591:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1590]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1585:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1591]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1586:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1598]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1587:[0-9]+]] = "riscv.addw"(%[[v1586]], %[[v1585]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1588:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1587]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1583:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1588]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1594]], %[[v1583]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1580:[0-9]+]] = "riscv.sh2add"(%[[v2851]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1576:[0-9]+]] = "riscv.lw"(%[[v1580]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1577:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1576]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1573:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1569:[0-9]+]] = "riscv.lw"(%[[v1573]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1570:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1569]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1564:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1570]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1565:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1577]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1566:[0-9]+]] = "riscv.xor"(%[[v1565]], %[[v1564]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1567:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1566]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1562:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1567]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1573]], %[[v1562]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1559:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1555:[0-9]+]] = "riscv.lw"(%[[v1559]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1556:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1555]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1550:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1556]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1551:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1552:[0-9]+]] = "riscv.sllw"(%[[v1550]], %[[v1551]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1553:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1552]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1546:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1556]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1547:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1548:[0-9]+]] = "riscv.srlw"(%[[v1546]], %[[v1547]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1549:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1548]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1542:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1553]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1543:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1549]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1544:[0-9]+]] = "riscv.or"(%[[v1543]], %[[v1542]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1545:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1544]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1540:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1536:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1545]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1540]], %[[v1536]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1533:[0-9]+]] = "riscv.sh2add"(%[[v3127]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1529:[0-9]+]] = "riscv.lw"(%[[v1533]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1530:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1529]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1526:[0-9]+]] = "riscv.sh2add"(%[[v2209]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1522:[0-9]+]] = "riscv.lw"(%[[v1526]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1523:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1522]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1517:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1523]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1518:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1530]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1519:[0-9]+]] = "riscv.addw"(%[[v1518]], %[[v1517]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1520:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1519]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1515:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1520]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1526]], %[[v1515]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1512:[0-9]+]] = "riscv.sh2add"(%[[v2209]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1508:[0-9]+]] = "riscv.lw"(%[[v1512]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1509:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1508]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1505:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1501:[0-9]+]] = "riscv.lw"(%[[v1505]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1502:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1501]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1496:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1502]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1497:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1509]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1498:[0-9]+]] = "riscv.xor"(%[[v1497]], %[[v1496]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1499:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1498]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1494:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1499]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1505]], %[[v1494]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1491:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1487:[0-9]+]] = "riscv.lw"(%[[v1491]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1488:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1487]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1482:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1488]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1483:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1484:[0-9]+]] = "riscv.sllw"(%[[v1482]], %[[v1483]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1485:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1484]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1478:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1488]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1479:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1480:[0-9]+]] = "riscv.srlw"(%[[v1478]], %[[v1479]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1481:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1480]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1474:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1485]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1475:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1481]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1476:[0-9]+]] = "riscv.or"(%[[v1475]], %[[v1474]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1477:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1476]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1472:[0-9]+]] = "riscv.sh2add"(%[[v2577]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1468:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1477]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1472]], %[[v1468]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1465:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1461:[0-9]+]] = "riscv.lw"(%[[v1465]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1462:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1461]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1458:[0-9]+]] = "riscv.sh2add"(%[[v2567]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1454:[0-9]+]] = "riscv.lw"(%[[v1458]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1455:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1454]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1449:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1455]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1450:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1462]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1451:[0-9]+]] = "riscv.addw"(%[[v1450]], %[[v1449]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1452:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1451]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1447:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1452]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1458]], %[[v1447]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1444:[0-9]+]] = "riscv.sh2add"(%[[v2567]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1440:[0-9]+]] = "riscv.lw"(%[[v1444]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1441:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1440]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1437:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1433:[0-9]+]] = "riscv.lw"(%[[v1437]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1434:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1433]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1428:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1434]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1429:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1441]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1430:[0-9]+]] = "riscv.xor"(%[[v1429]], %[[v1428]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1431:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1430]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1426:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1431]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1437]], %[[v1426]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1423:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1419:[0-9]+]] = "riscv.lw"(%[[v1423]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1420:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1419]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1414:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1420]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1415:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1416:[0-9]+]] = "riscv.sllw"(%[[v1414]], %[[v1415]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1417:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1416]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1410:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1420]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1411:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1412:[0-9]+]] = "riscv.srlw"(%[[v1410]], %[[v1411]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1413:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1412]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1406:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1417]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1407:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1413]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1408:[0-9]+]] = "riscv.or"(%[[v1407]], %[[v1406]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1409:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1408]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1404:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1400:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1409]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1404]], %[[v1400]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1397:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1393:[0-9]+]] = "riscv.lw"(%[[v1397]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1394:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1393]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1390:[0-9]+]] = "riscv.sh2add"(%[[v3073]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1386:[0-9]+]] = "riscv.lw"(%[[v1390]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1387:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1386]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1381:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1387]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1382:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1394]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1383:[0-9]+]] = "riscv.addw"(%[[v1382]], %[[v1381]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1384:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1383]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1379:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1384]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1390]], %[[v1379]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1376:[0-9]+]] = "riscv.sh2add"(%[[v3073]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1372:[0-9]+]] = "riscv.lw"(%[[v1376]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1373:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1372]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1369:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1365:[0-9]+]] = "riscv.lw"(%[[v1369]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1366:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1365]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1360:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1366]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1361:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1373]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1362:[0-9]+]] = "riscv.xor"(%[[v1361]], %[[v1360]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1363:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1362]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1358:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1363]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1369]], %[[v1358]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1355:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1351:[0-9]+]] = "riscv.lw"(%[[v1355]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1352:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1351]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1346:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1352]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1347:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1348:[0-9]+]] = "riscv.sllw"(%[[v1346]], %[[v1347]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1349:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1348]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1342:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1352]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1343:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1344:[0-9]+]] = "riscv.srlw"(%[[v1342]], %[[v1343]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1345:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1344]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1338:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1349]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1339:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1345]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1340:[0-9]+]] = "riscv.or"(%[[v1339]], %[[v1338]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1341:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1340]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1336:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1332:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1341]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1336]], %[[v1332]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1329:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1325:[0-9]+]] = "riscv.lw"(%[[v1329]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1326:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1325]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1322:[0-9]+]] = "riscv.sh2add"(%[[v2567]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1318:[0-9]+]] = "riscv.lw"(%[[v1322]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1319:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1318]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1313:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1319]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1314:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1326]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1315:[0-9]+]] = "riscv.addw"(%[[v1314]], %[[v1313]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1316:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1315]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1311:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1316]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1322]], %[[v1311]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1308:[0-9]+]] = "riscv.sh2add"(%[[v2567]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1304:[0-9]+]] = "riscv.lw"(%[[v1308]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1305:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1304]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1301:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1297:[0-9]+]] = "riscv.lw"(%[[v1301]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1298:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1297]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1292:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1298]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1293:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1305]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1294:[0-9]+]] = "riscv.xor"(%[[v1293]], %[[v1292]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1295:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1294]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1290:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1295]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1301]], %[[v1290]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1287:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1283:[0-9]+]] = "riscv.lw"(%[[v1287]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1284:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1283]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1278:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1284]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1279:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1280:[0-9]+]] = "riscv.sllw"(%[[v1278]], %[[v1279]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1281:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1280]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1274:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1284]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1275:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1276:[0-9]+]] = "riscv.srlw"(%[[v1274]], %[[v1275]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1277:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1276]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1270:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1281]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1271:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1277]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1272:[0-9]+]] = "riscv.or"(%[[v1271]], %[[v1270]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1273:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1272]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1268:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1264:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1273]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1268]], %[[v1264]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1261:[0-9]+]] = "riscv.sh2add"(%[[v2827]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1257:[0-9]+]] = "riscv.lw"(%[[v1261]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1258:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1257]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1254:[0-9]+]] = "riscv.sh2add"(%[[v3073]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1250:[0-9]+]] = "riscv.lw"(%[[v1254]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1251:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1250]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1245:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1251]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1246:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1258]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1247:[0-9]+]] = "riscv.addw"(%[[v1246]], %[[v1245]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1248:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1247]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1243:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1248]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1254]], %[[v1243]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1240:[0-9]+]] = "riscv.sh2add"(%[[v3073]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1236:[0-9]+]] = "riscv.lw"(%[[v1240]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1237:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1236]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1233:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1229:[0-9]+]] = "riscv.lw"(%[[v1233]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1230:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1229]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1224:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1230]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1225:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1237]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1226:[0-9]+]] = "riscv.xor"(%[[v1225]], %[[v1224]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1227:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1226]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1222:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1227]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1233]], %[[v1222]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1219:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1215:[0-9]+]] = "riscv.lw"(%[[v1219]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1216:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1215]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1210:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1216]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1211:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1212:[0-9]+]] = "riscv.sllw"(%[[v1210]], %[[v1211]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1213:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1212]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1206:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1216]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1207:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1208:[0-9]+]] = "riscv.srlw"(%[[v1206]], %[[v1207]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1209:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1208]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1202:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1213]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1203:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1209]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1204:[0-9]+]] = "riscv.or"(%[[v1203]], %[[v1202]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1205:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1204]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1200:[0-9]+]] = "riscv.sh2add"(%[[v2293]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1196:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1205]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1200]], %[[v1196]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1193:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1189:[0-9]+]] = "riscv.lw"(%[[v1193]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1190:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1189]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1186:[0-9]+]] = "riscv.sh2add"(%[[v2283]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1182:[0-9]+]] = "riscv.lw"(%[[v1186]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1183:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1182]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1177:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1183]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1178:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1190]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1179:[0-9]+]] = "riscv.addw"(%[[v1178]], %[[v1177]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1180:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1179]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1175:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1180]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1186]], %[[v1175]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1172:[0-9]+]] = "riscv.sh2add"(%[[v2283]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1168:[0-9]+]] = "riscv.lw"(%[[v1172]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1169:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1168]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1165:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1161:[0-9]+]] = "riscv.lw"(%[[v1165]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1162:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1161]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1156:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1162]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1157:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1169]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1158:[0-9]+]] = "riscv.xor"(%[[v1157]], %[[v1156]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1159:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1158]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1154:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1159]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1165]], %[[v1154]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1151:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1147:[0-9]+]] = "riscv.lw"(%[[v1151]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1148:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1147]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1142:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1148]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1143:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1144:[0-9]+]] = "riscv.sllw"(%[[v1142]], %[[v1143]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1145:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1144]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1138:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1148]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1139:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3100]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1140:[0-9]+]] = "riscv.srlw"(%[[v1138]], %[[v1139]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1141:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1140]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1134:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1145]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1135:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1141]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1136:[0-9]+]] = "riscv.or"(%[[v1135]], %[[v1134]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1137:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1136]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1132:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1128:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1137]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1132]], %[[v1128]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1125:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1121:[0-9]+]] = "riscv.lw"(%[[v1125]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1122:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1121]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1118:[0-9]+]] = "riscv.sh2add"(%[[v2777]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1114:[0-9]+]] = "riscv.lw"(%[[v1118]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1115:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1114]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1109:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1115]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1110:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1122]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1111:[0-9]+]] = "riscv.addw"(%[[v1110]], %[[v1109]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1112:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1111]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1107:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1112]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1118]], %[[v1107]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1104:[0-9]+]] = "riscv.sh2add"(%[[v2777]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1100:[0-9]+]] = "riscv.lw"(%[[v1104]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1101:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1100]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1097:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1093:[0-9]+]] = "riscv.lw"(%[[v1097]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1094:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1093]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1088:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1094]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1089:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1101]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1090:[0-9]+]] = "riscv.xor"(%[[v1089]], %[[v1088]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1091:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1090]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1086:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1091]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1097]], %[[v1086]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1083:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1079:[0-9]+]] = "riscv.lw"(%[[v1083]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1080:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1079]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1074:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1080]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1075:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3427]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1076:[0-9]+]] = "riscv.sllw"(%[[v1074]], %[[v1075]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1077:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1076]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1070:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1080]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1071:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3025]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1072:[0-9]+]] = "riscv.srlw"(%[[v1070]], %[[v1071]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1073:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1072]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1066:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1077]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1067:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1073]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1068:[0-9]+]] = "riscv.or"(%[[v1067]], %[[v1066]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1069:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1068]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1064:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1060:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1069]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1064]], %[[v1060]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1057:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1053:[0-9]+]] = "riscv.lw"(%[[v1057]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1054:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1053]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1050:[0-9]+]] = "riscv.sh2add"(%[[v2283]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1046:[0-9]+]] = "riscv.lw"(%[[v1050]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1047:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1046]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1041:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1047]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1042:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1054]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1043:[0-9]+]] = "riscv.addw"(%[[v1042]], %[[v1041]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1044:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1043]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1039:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1044]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1050]], %[[v1039]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1036:[0-9]+]] = "riscv.sh2add"(%[[v2283]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1032:[0-9]+]] = "riscv.lw"(%[[v1036]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1033:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1032]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1029:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1025:[0-9]+]] = "riscv.lw"(%[[v1029]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1026:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1025]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1020:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1026]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1021:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1033]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1022:[0-9]+]] = "riscv.xor"(%[[v1021]], %[[v1020]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1023:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1022]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1018:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1023]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v1029]], %[[v1018]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v1015:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1011:[0-9]+]] = "riscv.lw"(%[[v1015]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1012:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1011]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1006:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1012]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1007:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1008:[0-9]+]] = "riscv.sllw"(%[[v1006]], %[[v1007]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1009:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1008]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v1002:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1012]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1003:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2953]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1004:[0-9]+]] = "riscv.srlw"(%[[v1002]], %[[v1003]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1005:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1004]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v998:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1009]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v999:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1005]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v1000:[0-9]+]] = "riscv.or"(%[[v999]], %[[v998]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v1001:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1000]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v996:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v992:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v1001]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v996]], %[[v992]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v989:[0-9]+]] = "riscv.sh2add"(%[[v2543]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v985:[0-9]+]] = "riscv.lw"(%[[v989]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v986:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v985]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v982:[0-9]+]] = "riscv.sh2add"(%[[v2777]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v978:[0-9]+]] = "riscv.lw"(%[[v982]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v979:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v978]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v973:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v979]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v974:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v986]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v975:[0-9]+]] = "riscv.addw"(%[[v974]], %[[v973]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v976:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v975]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v971:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v976]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v982]], %[[v971]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v968:[0-9]+]] = "riscv.sh2add"(%[[v2777]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v964:[0-9]+]] = "riscv.lw"(%[[v968]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v965:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v964]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v961:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v957:[0-9]+]] = "riscv.lw"(%[[v961]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v958:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v957]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v952:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v958]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v953:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v965]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v954:[0-9]+]] = "riscv.xor"(%[[v953]], %[[v952]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v955:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v954]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v950:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v955]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v961]], %[[v950]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v947:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v943:[0-9]+]] = "riscv.lw"(%[[v947]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v944:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v943]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v938:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v944]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v939:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3423]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v940:[0-9]+]] = "riscv.sllw"(%[[v938]], %[[v939]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v941:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v940]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v934:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v944]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v935:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v2881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v936:[0-9]+]] = "riscv.srlw"(%[[v934]], %[[v935]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v937:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v936]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v930:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v941]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v931:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v937]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v932:[0-9]+]] = "riscv.or"(%[[v931]], %[[v930]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v933:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v932]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v928:[0-9]+]] = "riscv.sh2add"(%[[v3161]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v924:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v933]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v928]], %[[v924]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb763:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb763]]():
// CHECK-NEXT:         %[[v921:[0-9]+]] = "riscv.add"(%[[v3458]], %[[varg129_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v921]]) [^[[bb129]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb133]]():
// CHECK-NEXT:         "riscv_cf.branch"(%[[v3462]]) [^[[bb767:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb767]](%[[varg767_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v917:[0-9]+]] = "riscv.slt"(%[[varg767_0]], %[[v3442]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v918:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v917]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v806:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v918]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v806]]) [^[[bb770:[0-9]+]], ^[[bb771:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb770]]():
// CHECK-NEXT:         %[[v913:[0-9]+]] = "riscv.mul"(%[[varg767_0]], %[[v3438]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v909:[0-9]+]] = "riscv.add"(%[[varg7_3]], %[[v913]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v905:[0-9]+]] = "riscv.sh2add"(%[[varg767_0]], %[[varg7_5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v901:[0-9]+]] = "riscv.lw"(%[[v905]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v902:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v898:[0-9]+]] = "riscv.sh2add"(%[[varg767_0]], %[[varg7_4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v894:[0-9]+]] = "riscv.lw"(%[[v898]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v895:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v894]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v889:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v902]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v890:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v895]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v891:[0-9]+]] = "riscv.addw"(%[[v890]], %[[v889]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v892:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v891]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v887:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v892]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v888:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v887]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v885:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v888]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         "riscv.sb"(%[[v909]], %[[v885]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v880:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v892]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v881:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v882:[0-9]+]] = "riscv.srlw"(%[[v880]], %[[v881]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v883:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v882]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v878:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v883]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v879:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v878]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v876:[0-9]+]] = "riscv.add"(%[[v909]], %[[v3458]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v872:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v879]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         "riscv.sb"(%[[v876]], %[[v872]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v867:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v892]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v868:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3435]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v869:[0-9]+]] = "riscv.srlw"(%[[v867]], %[[v868]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v870:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v869]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v865:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v870]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v866:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v865]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v863:[0-9]+]] = "riscv.add"(%[[v909]], %[[v3454]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v859:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v866]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         "riscv.sb"(%[[v863]], %[[v859]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v854:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v892]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v855:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v3433]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v856:[0-9]+]] = "riscv.srlw"(%[[v854]], %[[v855]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v857:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v856]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v852:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v857]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v853:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v852]]) : (!riscv.reg) -> i8
// CHECK-NEXT:         %[[v850:[0-9]+]] = "riscv.add"(%[[v909]], %[[v3450]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v846:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v853]]) : (i8) -> !riscv.reg
// CHECK-NEXT:         "riscv.sb"(%[[v850]], %[[v846]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb794:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb794]]():
// CHECK-NEXT:         %[[v843:[0-9]+]] = "riscv.add"(%[[v3458]], %[[varg767_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v843]]) [^[[bb767]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb771]]():
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()
