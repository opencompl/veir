// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 1 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 4 : i32>]}> : () -> ()
    "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, always_inline, "arg_attrs" = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], "frame_pointer" = #llvm.framePointerKind<"non-leaf-no-reserve">, "function_type" = !llvm.func<void (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr)>, "linkage" = #llvm.linkage<external>, no_unwind, "passthrough" = ["ssp", ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "apple-m1"]], "sym_name" = "sha256_block", "target_cpu" = "apple-m1", "target_features" = #llvm.target_features<["+aes", "+altnzcv", "+ccdp", "+ccidx", "+ccpp", "+complxnum", "+crc", "+dit", "+dotprod", "+flagm", "+fp-armv8", "+fp16fml", "+fptoint", "+fullfp16", "+jsconv", "+lse", "+neon", "+pauth", "+perfmon", "+predres", "+ras", "+rcpc", "+rdm", "+sb", "+sha2", "+sha3", "+specrestrict", "+ssbs", "+v8.1a", "+v8.2a", "+v8.3a", "+v8.4a", "+v8a"]>, "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<sync>, "visibility_" = 0 : i64}> ({
      ^7(%arg7_0 : !llvm.ptr, %arg7_1 : !llvm.ptr, %arg7_2 : !llvm.ptr, %arg7_3 : !llvm.ptr):
        %8 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
        %9 = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
        %10 = "llvm.mlir.constant"() <{"value" = 64 : i32}> : () -> i32
        %11 = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
        %12 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
        %13 = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
        %14 = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
        %15 = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
        %16 = "llvm.mlir.constant"() <{"value" = 5 : i64}> : () -> i64
        %17 = "llvm.mlir.constant"() <{"value" = 6 : i64}> : () -> i64
        %18 = "llvm.mlir.constant"() <{"value" = 7 : i64}> : () -> i64
        %19 = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
        %20 = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
        %21 = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
        %22 = "llvm.mlir.constant"() <{"value" = 25 : i32}> : () -> i32
        %23 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %24 = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
        %25 = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
        %26 = "llvm.mlir.constant"() <{"value" = 22 : i32}> : () -> i32
        %27 = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
        %28 = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
        %29 = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
        %30 = "llvm.mlir.constant"() <{"value" = 18 : i32}> : () -> i32
        %31 = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
        %32 = "llvm.mlir.constant"() <{"value" = 17 : i32}> : () -> i32
        %33 = "llvm.mlir.constant"() <{"value" = 19 : i32}> : () -> i32
        %34 = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
        "llvm.br"(%8) [^35] : (i32) -> ()
      ^35(%arg35_0 : i32):
        %37 = "llvm.icmp"(%arg35_0, %9) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%37) [^38, ^39] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^38():
        %41 = "llvm.sext"(%arg35_0) : (i32) -> i64
        %42 = "llvm.getelementptr"(%arg7_1, %41) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %43 = "llvm.load"(%42) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %45 = "llvm.getelementptr"(%arg7_3, %41) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%43, %45) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"() [^47] : () -> ()
      ^47():
        %49 = "llvm.add"(%arg35_0, %27) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%49) [^35] : (i32) -> ()
      ^39():
        "llvm.br"(%9) [^51] : (i32) -> ()
      ^51(%arg51_0 : i32):
        %53 = "llvm.icmp"(%arg51_0, %10) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%53) [^54, ^55] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^54():
        %57 = "llvm.sub"(%arg51_0, %28) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %58 = "llvm.sext"(%57) : (i32) -> i64
        %59 = "llvm.getelementptr"(%arg7_3, %58) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %60 = "llvm.load"(%59) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %61 = "llvm.lshr"(%60, %29) : (i32, i32) -> i32
        %62 = "llvm.sub"(%20, %29) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %63 = "llvm.shl"(%60, %62) : (i32, i32) -> i32
        %64 = "llvm.or"(%61, %63) : (i32, i32) -> i32
        %67 = "llvm.getelementptr"(%arg7_3, %58) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %68 = "llvm.load"(%67) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %69 = "llvm.lshr"(%68, %30) : (i32, i32) -> i32
        %70 = "llvm.sub"(%20, %30) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %71 = "llvm.shl"(%68, %70) : (i32, i32) -> i32
        %72 = "llvm.or"(%69, %71) : (i32, i32) -> i32
        %73 = "llvm.xor"(%64, %72) : (i32, i32) -> i32
        %76 = "llvm.getelementptr"(%arg7_3, %58) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %77 = "llvm.load"(%76) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %78 = "llvm.lshr"(%77, %31) : (i32, i32) -> i32
        %79 = "llvm.xor"(%73, %78) : (i32, i32) -> i32
        %80 = "llvm.sub"(%arg51_0, %24) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %81 = "llvm.sext"(%80) : (i32) -> i64
        %82 = "llvm.getelementptr"(%arg7_3, %81) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %83 = "llvm.load"(%82) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %84 = "llvm.lshr"(%83, %32) : (i32, i32) -> i32
        %85 = "llvm.sub"(%20, %32) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %86 = "llvm.shl"(%83, %85) : (i32, i32) -> i32
        %87 = "llvm.or"(%84, %86) : (i32, i32) -> i32
        %90 = "llvm.getelementptr"(%arg7_3, %81) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %91 = "llvm.load"(%90) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %92 = "llvm.lshr"(%91, %33) : (i32, i32) -> i32
        %93 = "llvm.sub"(%20, %33) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %94 = "llvm.shl"(%91, %93) : (i32, i32) -> i32
        %95 = "llvm.or"(%92, %94) : (i32, i32) -> i32
        %96 = "llvm.xor"(%87, %95) : (i32, i32) -> i32
        %99 = "llvm.getelementptr"(%arg7_3, %81) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %100 = "llvm.load"(%99) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %101 = "llvm.lshr"(%100, %34) : (i32, i32) -> i32
        %102 = "llvm.xor"(%96, %101) : (i32, i32) -> i32
        %103 = "llvm.sub"(%arg51_0, %9) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %104 = "llvm.sext"(%103) : (i32) -> i64
        %105 = "llvm.getelementptr"(%arg7_3, %104) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %106 = "llvm.load"(%105) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %107 = "llvm.add"(%106, %79) : (i32, i32) -> i32
        %108 = "llvm.sub"(%arg51_0, %29) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %109 = "llvm.sext"(%108) : (i32) -> i64
        %110 = "llvm.getelementptr"(%arg7_3, %109) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %111 = "llvm.load"(%110) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %112 = "llvm.add"(%107, %111) : (i32, i32) -> i32
        %113 = "llvm.add"(%112, %102) : (i32, i32) -> i32
        %114 = "llvm.sext"(%arg51_0) : (i32) -> i64
        %115 = "llvm.getelementptr"(%arg7_3, %114) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%113, %115) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.br"() [^117] : () -> ()
      ^117():
        %119 = "llvm.add"(%arg51_0, %27) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%119) [^51] : (i32) -> ()
      ^55():
        %121 = "llvm.getelementptr"(%arg7_0, %11) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %122 = "llvm.load"(%121) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %123 = "llvm.getelementptr"(%arg7_0, %12) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %124 = "llvm.load"(%123) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %125 = "llvm.getelementptr"(%arg7_0, %13) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %126 = "llvm.load"(%125) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %127 = "llvm.getelementptr"(%arg7_0, %14) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %128 = "llvm.load"(%127) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %129 = "llvm.getelementptr"(%arg7_0, %15) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %130 = "llvm.load"(%129) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %131 = "llvm.getelementptr"(%arg7_0, %16) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %132 = "llvm.load"(%131) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %133 = "llvm.getelementptr"(%arg7_0, %17) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %134 = "llvm.load"(%133) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %135 = "llvm.getelementptr"(%arg7_0, %18) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %136 = "llvm.load"(%135) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        "llvm.br"(%130, %132, %134, %136, %8, %128, %126, %124, %122) [^137] : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
      ^137(%arg137_0 : i32, %arg137_1 : i32, %arg137_2 : i32, %arg137_3 : i32, %arg137_4 : i32, %arg137_5 : i32, %arg137_6 : i32, %arg137_7 : i32, %arg137_8 : i32):
        %139 = "llvm.icmp"(%arg137_4, %10) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
        "llvm.cond_br"(%139) [^140, ^141] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^140():
        %143 = "llvm.lshr"(%arg137_0, %19) : (i32, i32) -> i32
        %144 = "llvm.sub"(%20, %19) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %145 = "llvm.shl"(%arg137_0, %144) : (i32, i32) -> i32
        %146 = "llvm.or"(%143, %145) : (i32, i32) -> i32
        %147 = "llvm.lshr"(%arg137_0, %21) : (i32, i32) -> i32
        %148 = "llvm.sub"(%20, %21) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %149 = "llvm.shl"(%arg137_0, %148) : (i32, i32) -> i32
        %150 = "llvm.or"(%147, %149) : (i32, i32) -> i32
        %151 = "llvm.xor"(%146, %150) : (i32, i32) -> i32
        %152 = "llvm.lshr"(%arg137_0, %22) : (i32, i32) -> i32
        %153 = "llvm.sub"(%20, %22) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %154 = "llvm.shl"(%arg137_0, %153) : (i32, i32) -> i32
        %155 = "llvm.or"(%152, %154) : (i32, i32) -> i32
        %156 = "llvm.xor"(%151, %155) : (i32, i32) -> i32
        %157 = "llvm.and"(%arg137_0, %arg137_1) : (i32, i32) -> i32
        %158 = "llvm.xor"(%arg137_0, %23) : (i32, i32) -> i32
        %159 = "llvm.and"(%158, %arg137_2) : (i32, i32) -> i32
        %160 = "llvm.xor"(%157, %159) : (i32, i32) -> i32
        %161 = "llvm.add"(%arg137_3, %156) : (i32, i32) -> i32
        %162 = "llvm.add"(%161, %160) : (i32, i32) -> i32
        %163 = "llvm.sext"(%arg137_4) : (i32) -> i64
        %164 = "llvm.getelementptr"(%arg7_2, %163) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %165 = "llvm.load"(%164) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %166 = "llvm.add"(%162, %165) : (i32, i32) -> i32
        %168 = "llvm.getelementptr"(%arg7_3, %163) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %169 = "llvm.load"(%168) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %170 = "llvm.add"(%166, %169) : (i32, i32) -> i32
        %171 = "llvm.lshr"(%arg137_8, %24) : (i32, i32) -> i32
        %172 = "llvm.sub"(%20, %24) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %173 = "llvm.shl"(%arg137_8, %172) : (i32, i32) -> i32
        %174 = "llvm.or"(%171, %173) : (i32, i32) -> i32
        %175 = "llvm.lshr"(%arg137_8, %25) : (i32, i32) -> i32
        %176 = "llvm.sub"(%20, %25) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %177 = "llvm.shl"(%arg137_8, %176) : (i32, i32) -> i32
        %178 = "llvm.or"(%175, %177) : (i32, i32) -> i32
        %179 = "llvm.xor"(%174, %178) : (i32, i32) -> i32
        %180 = "llvm.lshr"(%arg137_8, %26) : (i32, i32) -> i32
        %181 = "llvm.sub"(%20, %26) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        %182 = "llvm.shl"(%arg137_8, %181) : (i32, i32) -> i32
        %183 = "llvm.or"(%180, %182) : (i32, i32) -> i32
        %184 = "llvm.xor"(%179, %183) : (i32, i32) -> i32
        %185 = "llvm.and"(%arg137_8, %arg137_7) : (i32, i32) -> i32
        %186 = "llvm.and"(%arg137_8, %arg137_6) : (i32, i32) -> i32
        %187 = "llvm.xor"(%185, %186) : (i32, i32) -> i32
        %188 = "llvm.and"(%arg137_7, %arg137_6) : (i32, i32) -> i32
        %189 = "llvm.xor"(%187, %188) : (i32, i32) -> i32
        %190 = "llvm.add"(%184, %189) : (i32, i32) -> i32
        %191 = "llvm.add"(%arg137_5, %170) : (i32, i32) -> i32
        %192 = "llvm.add"(%170, %190) : (i32, i32) -> i32
        "llvm.br"() [^193] : () -> ()
      ^193():
        %195 = "llvm.add"(%arg137_4, %27) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
        "llvm.br"(%191, %arg137_0, %arg137_1, %arg137_2, %195, %arg137_6, %arg137_7, %arg137_8, %192) [^137] : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
      ^141():
        %197 = "llvm.getelementptr"(%arg7_0, %11) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %198 = "llvm.load"(%197) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %199 = "llvm.add"(%198, %arg137_8) : (i32, i32) -> i32
        "llvm.store"(%199, %197) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %201 = "llvm.getelementptr"(%arg7_0, %12) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %202 = "llvm.load"(%201) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %203 = "llvm.add"(%202, %arg137_7) : (i32, i32) -> i32
        "llvm.store"(%203, %201) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %205 = "llvm.getelementptr"(%arg7_0, %13) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %206 = "llvm.load"(%205) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %207 = "llvm.add"(%206, %arg137_6) : (i32, i32) -> i32
        "llvm.store"(%207, %205) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %209 = "llvm.getelementptr"(%arg7_0, %14) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %210 = "llvm.load"(%209) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %211 = "llvm.add"(%210, %arg137_5) : (i32, i32) -> i32
        "llvm.store"(%211, %209) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %213 = "llvm.getelementptr"(%arg7_0, %15) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %214 = "llvm.load"(%213) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %215 = "llvm.add"(%214, %arg137_0) : (i32, i32) -> i32
        "llvm.store"(%215, %213) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %217 = "llvm.getelementptr"(%arg7_0, %16) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %218 = "llvm.load"(%217) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %219 = "llvm.add"(%218, %arg137_1) : (i32, i32) -> i32
        "llvm.store"(%219, %217) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %221 = "llvm.getelementptr"(%arg7_0, %17) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %222 = "llvm.load"(%221) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %223 = "llvm.add"(%222, %arg137_2) : (i32, i32) -> i32
        "llvm.store"(%223, %221) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        %225 = "llvm.getelementptr"(%arg7_0, %18) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %226 = "llvm.load"(%225) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
        %227 = "llvm.add"(%226, %arg137_3) : (i32, i32) -> i32
        "llvm.store"(%227, %225) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "o", "dlti.legal_int_widths" = array<i32: 32, 64>, "dlti.stack_alignment" = 128 : i64, "dlti.function_pointer_alignment" = #dlti.function_pointer_alignment<32, function_dependent = true>>, "llvm.ident" = "Homebrew clang version 22.1.7", "llvm.module_asm" = [], "llvm.target_triple" = "arm64-apple-macosx26.0.0"} : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^[[bb4:[0-9]+]]():
// CHECK-NEXT:     "llvm.module_flags"() {{.*}} : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}"sym_name" = "sha256_block"{{.*}}}> ({
// CHECK-NEXT:       ^[[bb7:[0-9]+]](%[[varg7_0:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_1:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_2:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_3:[a-zA-Z0-9_]+]] : !llvm.ptr):
// CHECK-NEXT:         %[[v8:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:         %[[v9:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 16 : i32}> : () -> i32
// CHECK-NEXT:         %[[v10:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 64 : i32}> : () -> i32
// CHECK-NEXT:         %[[v11:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:         %[[v12:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[v13:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:         %[[v14:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK-NEXT:         %[[v15:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
// CHECK-NEXT:         %[[v16:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 5 : i64}> : () -> i64
// CHECK-NEXT:         %[[v17:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 6 : i64}> : () -> i64
// CHECK-NEXT:         %[[v18:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 7 : i64}> : () -> i64
// CHECK-NEXT:         %[[v19:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 6 : i32}> : () -> i32
// CHECK-NEXT:         %[[v20:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 32 : i32}> : () -> i32
// CHECK-NEXT:         %[[v21:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
// CHECK-NEXT:         %[[v22:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 25 : i32}> : () -> i32
// CHECK-NEXT:         %[[v23:[0-9]+]] = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v24:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
// CHECK-NEXT:         %[[v25:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:         %[[v26:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 22 : i32}> : () -> i32
// CHECK-NEXT:         %[[v27:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:         %[[v28:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 15 : i32}> : () -> i32
// CHECK-NEXT:         %[[v29:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:         %[[v30:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 18 : i32}> : () -> i32
// CHECK-NEXT:         %[[v31:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:         %[[v32:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 17 : i32}> : () -> i32
// CHECK-NEXT:         %[[v33:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 19 : i32}> : () -> i32
// CHECK-NEXT:         %[[v34:[0-9]+]] = "llvm.mlir.constant"() <{"value" = 10 : i32}> : () -> i32
// CHECK-NEXT:         "llvm.br"(%[[v8]]) [^[[bb35:[0-9]+]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb35]](%[[varg35_0:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT:         %[[v37:[0-9]+]] = "llvm.icmp"(%[[varg35_0]], %[[v9]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v37]]) [^[[bb38:[0-9]+]], ^[[bb39:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb38]]():
// CHECK-NEXT:         %[[v41:[0-9]+]] = "llvm.sext"(%[[varg35_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v42:[0-9]+]] = "llvm.getelementptr"(%[[varg7_1]], %[[v41]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v43:[0-9]+]] = "llvm.load"(%[[v42]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v44:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v41]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v43]], %[[v44]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb46:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb46]]():
// CHECK-NEXT:         %[[v48:[0-9]+]] = "llvm.add"(%[[varg35_0]], %[[v27]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v48]]) [^[[bb35]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb39]]():
// CHECK-NEXT:         "llvm.br"(%[[v9]]) [^[[bb50:[0-9]+]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb50]](%[[varg50_0:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT:         %[[v52:[0-9]+]] = "llvm.icmp"(%[[varg50_0]], %[[v10]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v52]]) [^[[bb53:[0-9]+]], ^[[bb54:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb53]]():
// CHECK-NEXT:         %[[v56:[0-9]+]] = "llvm.sub"(%[[varg50_0]], %[[v28]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v57:[0-9]+]] = "llvm.sext"(%[[v56]]) : (i32) -> i64
// CHECK-NEXT:         %[[v58:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v57]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v59:[0-9]+]] = "llvm.load"(%[[v58]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v60:[0-9]+]] = "llvm.lshr"(%[[v59]], %[[v29]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v61:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v29]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v62:[0-9]+]] = "llvm.shl"(%[[v59]], %[[v61]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v63:[0-9]+]] = "llvm.or"(%[[v60]], %[[v62]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v64:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v57]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v65:[0-9]+]] = "llvm.load"(%[[v64]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v66:[0-9]+]] = "llvm.lshr"(%[[v65]], %[[v30]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v67:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v30]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v68:[0-9]+]] = "llvm.shl"(%[[v65]], %[[v67]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v69:[0-9]+]] = "llvm.or"(%[[v66]], %[[v68]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v70:[0-9]+]] = "llvm.xor"(%[[v63]], %[[v69]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v71:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v57]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v72:[0-9]+]] = "llvm.load"(%[[v71]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v73:[0-9]+]] = "llvm.lshr"(%[[v72]], %[[v31]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v74:[0-9]+]] = "llvm.xor"(%[[v70]], %[[v73]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v75:[0-9]+]] = "llvm.sub"(%[[varg50_0]], %[[v24]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v76:[0-9]+]] = "llvm.sext"(%[[v75]]) : (i32) -> i64
// CHECK-NEXT:         %[[v77:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v76]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v78:[0-9]+]] = "llvm.load"(%[[v77]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v79:[0-9]+]] = "llvm.lshr"(%[[v78]], %[[v32]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v80:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v32]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v81:[0-9]+]] = "llvm.shl"(%[[v78]], %[[v80]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v82:[0-9]+]] = "llvm.or"(%[[v79]], %[[v81]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v83:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v76]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v84:[0-9]+]] = "llvm.load"(%[[v83]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v85:[0-9]+]] = "llvm.lshr"(%[[v84]], %[[v33]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v86:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v33]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v87:[0-9]+]] = "llvm.shl"(%[[v84]], %[[v86]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v88:[0-9]+]] = "llvm.or"(%[[v85]], %[[v87]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v89:[0-9]+]] = "llvm.xor"(%[[v82]], %[[v88]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v90:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v76]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v91:[0-9]+]] = "llvm.load"(%[[v90]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v92:[0-9]+]] = "llvm.lshr"(%[[v91]], %[[v34]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v93:[0-9]+]] = "llvm.xor"(%[[v89]], %[[v92]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v94:[0-9]+]] = "llvm.sub"(%[[varg50_0]], %[[v9]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v95:[0-9]+]] = "llvm.sext"(%[[v94]]) : (i32) -> i64
// CHECK-NEXT:         %[[v96:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v95]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v97:[0-9]+]] = "llvm.load"(%[[v96]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v98:[0-9]+]] = "llvm.add"(%[[v97]], %[[v74]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v99:[0-9]+]] = "llvm.sub"(%[[varg50_0]], %[[v29]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v100:[0-9]+]] = "llvm.sext"(%[[v99]]) : (i32) -> i64
// CHECK-NEXT:         %[[v101:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v100]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v102:[0-9]+]] = "llvm.load"(%[[v101]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v103:[0-9]+]] = "llvm.add"(%[[v98]], %[[v102]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v104:[0-9]+]] = "llvm.add"(%[[v103]], %[[v93]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v105:[0-9]+]] = "llvm.sext"(%[[varg50_0]]) : (i32) -> i64
// CHECK-NEXT:         %[[v106:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v105]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[v104]], %[[v106]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^[[bb108:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb108]]():
// CHECK-NEXT:         %[[v110:[0-9]+]] = "llvm.add"(%[[varg50_0]], %[[v27]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v110]]) [^[[bb50]]] : (i32) -> ()
// CHECK-NEXT:       ^[[bb54]]():
// CHECK-NEXT:         %[[v112:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v11]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v113:[0-9]+]] = "llvm.load"(%[[v112]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v114:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v12]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v115:[0-9]+]] = "llvm.load"(%[[v114]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v116:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v13]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v117:[0-9]+]] = "llvm.load"(%[[v116]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v118:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v14]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v119:[0-9]+]] = "llvm.load"(%[[v118]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v120:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v15]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v121:[0-9]+]] = "llvm.load"(%[[v120]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v122:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v16]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v123:[0-9]+]] = "llvm.load"(%[[v122]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v124:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v17]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v125:[0-9]+]] = "llvm.load"(%[[v124]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v126:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v18]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v127:[0-9]+]] = "llvm.load"(%[[v126]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v121]], %[[v123]], %[[v125]], %[[v127]], %[[v8]], %[[v119]], %[[v117]], %[[v115]], %[[v113]]) [^[[bb128:[0-9]+]]] : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[bb128]](%[[varg128_0:[a-zA-Z0-9_]+]] : i32, %[[varg128_1:[a-zA-Z0-9_]+]] : i32, %[[varg128_2:[a-zA-Z0-9_]+]] : i32, %[[varg128_3:[a-zA-Z0-9_]+]] : i32, %[[varg128_4:[a-zA-Z0-9_]+]] : i32, %[[varg128_5:[a-zA-Z0-9_]+]] : i32, %[[varg128_6:[a-zA-Z0-9_]+]] : i32, %[[varg128_7:[a-zA-Z0-9_]+]] : i32, %[[varg128_8:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT:         %[[v130:[0-9]+]] = "llvm.icmp"(%[[varg128_4]], %[[v10]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[v130]]) [^[[bb131:[0-9]+]], ^[[bb132:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^[[bb131]]():
// CHECK-NEXT:         %[[v134:[0-9]+]] = "llvm.lshr"(%[[varg128_0]], %[[v19]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v135:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v19]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v136:[0-9]+]] = "llvm.shl"(%[[varg128_0]], %[[v135]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v137:[0-9]+]] = "llvm.or"(%[[v134]], %[[v136]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v138:[0-9]+]] = "llvm.lshr"(%[[varg128_0]], %[[v21]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v139:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v21]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v140:[0-9]+]] = "llvm.shl"(%[[varg128_0]], %[[v139]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v141:[0-9]+]] = "llvm.or"(%[[v138]], %[[v140]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v142:[0-9]+]] = "llvm.xor"(%[[v137]], %[[v141]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v143:[0-9]+]] = "llvm.lshr"(%[[varg128_0]], %[[v22]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v144:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v22]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v145:[0-9]+]] = "llvm.shl"(%[[varg128_0]], %[[v144]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v146:[0-9]+]] = "llvm.or"(%[[v143]], %[[v145]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v147:[0-9]+]] = "llvm.xor"(%[[v142]], %[[v146]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v148:[0-9]+]] = "llvm.and"(%[[varg128_0]], %[[varg128_1]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v149:[0-9]+]] = "llvm.xor"(%[[varg128_0]], %[[v23]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v150:[0-9]+]] = "llvm.and"(%[[v149]], %[[varg128_2]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v151:[0-9]+]] = "llvm.xor"(%[[v148]], %[[v150]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v152:[0-9]+]] = "llvm.add"(%[[varg128_3]], %[[v147]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v153:[0-9]+]] = "llvm.add"(%[[v152]], %[[v151]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v154:[0-9]+]] = "llvm.sext"(%[[varg128_4]]) : (i32) -> i64
// CHECK-NEXT:         %[[v155:[0-9]+]] = "llvm.getelementptr"(%[[varg7_2]], %[[v154]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v156:[0-9]+]] = "llvm.load"(%[[v155]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v157:[0-9]+]] = "llvm.add"(%[[v153]], %[[v156]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v158:[0-9]+]] = "llvm.getelementptr"(%[[varg7_3]], %[[v154]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v159:[0-9]+]] = "llvm.load"(%[[v158]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v160:[0-9]+]] = "llvm.add"(%[[v157]], %[[v159]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v161:[0-9]+]] = "llvm.lshr"(%[[varg128_8]], %[[v24]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v162:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v24]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v163:[0-9]+]] = "llvm.shl"(%[[varg128_8]], %[[v162]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v164:[0-9]+]] = "llvm.or"(%[[v161]], %[[v163]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v165:[0-9]+]] = "llvm.lshr"(%[[varg128_8]], %[[v25]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v166:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v25]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v167:[0-9]+]] = "llvm.shl"(%[[varg128_8]], %[[v166]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v168:[0-9]+]] = "llvm.or"(%[[v165]], %[[v167]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v169:[0-9]+]] = "llvm.xor"(%[[v164]], %[[v168]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v170:[0-9]+]] = "llvm.lshr"(%[[varg128_8]], %[[v26]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v171:[0-9]+]] = "llvm.sub"(%[[v20]], %[[v26]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         %[[v172:[0-9]+]] = "llvm.shl"(%[[varg128_8]], %[[v171]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v173:[0-9]+]] = "llvm.or"(%[[v170]], %[[v172]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v174:[0-9]+]] = "llvm.xor"(%[[v169]], %[[v173]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v175:[0-9]+]] = "llvm.and"(%[[varg128_8]], %[[varg128_7]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v176:[0-9]+]] = "llvm.and"(%[[varg128_8]], %[[varg128_6]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v177:[0-9]+]] = "llvm.xor"(%[[v175]], %[[v176]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v178:[0-9]+]] = "llvm.and"(%[[varg128_7]], %[[varg128_6]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v179:[0-9]+]] = "llvm.xor"(%[[v177]], %[[v178]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v180:[0-9]+]] = "llvm.add"(%[[v174]], %[[v179]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v181:[0-9]+]] = "llvm.add"(%[[varg128_5]], %[[v160]]) : (i32, i32) -> i32
// CHECK-NEXT:         %[[v182:[0-9]+]] = "llvm.add"(%[[v160]], %[[v180]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"() [^[[bb183:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb183]]():
// CHECK-NEXT:         %[[v185:[0-9]+]] = "llvm.add"(%[[varg128_4]], %[[v27]]) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.br"(%[[v181]], %[[varg128_0]], %[[varg128_1]], %[[varg128_2]], %[[v185]], %[[varg128_6]], %[[varg128_7]], %[[varg128_8]], %[[v182]]) [^[[bb128]]] : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[bb132]]():
// CHECK-NEXT:         %[[v187:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v11]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v188:[0-9]+]] = "llvm.load"(%[[v187]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v189:[0-9]+]] = "llvm.add"(%[[v188]], %[[varg128_8]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v189]], %[[v187]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v191:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v12]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v192:[0-9]+]] = "llvm.load"(%[[v191]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v193:[0-9]+]] = "llvm.add"(%[[v192]], %[[varg128_7]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v193]], %[[v191]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v195:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v13]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v196:[0-9]+]] = "llvm.load"(%[[v195]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v197:[0-9]+]] = "llvm.add"(%[[v196]], %[[varg128_6]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v197]], %[[v195]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v199:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v14]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v200:[0-9]+]] = "llvm.load"(%[[v199]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v201:[0-9]+]] = "llvm.add"(%[[v200]], %[[varg128_5]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v201]], %[[v199]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v203:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v15]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v204:[0-9]+]] = "llvm.load"(%[[v203]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v205:[0-9]+]] = "llvm.add"(%[[v204]], %[[varg128_0]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v205]], %[[v203]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v207:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v16]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v208:[0-9]+]] = "llvm.load"(%[[v207]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v209:[0-9]+]] = "llvm.add"(%[[v208]], %[[varg128_1]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v209]], %[[v207]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v211:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v17]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v212:[0-9]+]] = "llvm.load"(%[[v211]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v213:[0-9]+]] = "llvm.add"(%[[v212]], %[[varg128_2]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v213]], %[[v211]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[v215:[0-9]+]] = "llvm.getelementptr"(%[[varg7_0]], %[[v18]]) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[v216:[0-9]+]] = "llvm.load"(%[[v215]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:         %[[v217:[0-9]+]] = "llvm.add"(%[[v216]], %[[varg128_3]]) : (i32, i32) -> i32
// CHECK-NEXT:         "llvm.store"(%[[v217]], %[[v215]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()

