// RUN: veir-opt %s -p=isel-br-riscv64,isel-riscv64,reconcile-cast | filecheck %s

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
// CHECK-NEXT:       ^[[bb7:[0-9]+]](%[[varg7_0:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg7_1:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg7_2:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg7_3:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v924:[0-9]+]] = "riscv.li"() <{"value" = 0 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v925:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v924]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v922:[0-9]+]] = "riscv.li"() <{"value" = 16 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v923:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v922]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v920:[0-9]+]] = "riscv.li"() <{"value" = 64 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v921:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v920]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v918:[0-9]+]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v916:[0-9]+]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v914:[0-9]+]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v912:[0-9]+]] = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v910:[0-9]+]] = "riscv.li"() <{"value" = 4 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v908:[0-9]+]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v906:[0-9]+]] = "riscv.li"() <{"value" = 6 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v904:[0-9]+]] = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v902:[0-9]+]] = "riscv.li"() <{"value" = 6 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v903:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v902]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v900:[0-9]+]] = "riscv.li"() <{"value" = 32 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v901:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v900]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v898:[0-9]+]] = "riscv.li"() <{"value" = 11 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v899:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v898]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v896:[0-9]+]] = "riscv.li"() <{"value" = 25 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v897:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v896]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v894:[0-9]+]] = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v895:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v894]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v892:[0-9]+]] = "riscv.li"() <{"value" = 2 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v893:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v892]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v890:[0-9]+]] = "riscv.li"() <{"value" = 13 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v891:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v890]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v888:[0-9]+]] = "riscv.li"() <{"value" = 22 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v889:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v888]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v886:[0-9]+]] = "riscv.li"() <{"value" = 1 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v887:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v886]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v884:[0-9]+]] = "riscv.li"() <{"value" = 15 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v885:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v884]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v882:[0-9]+]] = "riscv.li"() <{"value" = 7 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v883:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v882]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v880:[0-9]+]] = "riscv.li"() <{"value" = 18 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v881:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v880]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v878:[0-9]+]] = "riscv.li"() <{"value" = 3 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v879:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v878]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v876:[0-9]+]] = "riscv.li"() <{"value" = 17 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v877:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v876]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v874:[0-9]+]] = "riscv.li"() <{"value" = 19 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v875:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v874]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v872:[0-9]+]] = "riscv.li"() <{"value" = 10 : i32}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v873:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v872]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v253:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v925]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v253]]) [^[[bb35:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb35]](%[[varg35_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v255:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg35_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v866:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v255]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v867:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v923]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v868:[0-9]+]] = "riscv.sextw"(%[[v866]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v869:[0-9]+]] = "riscv.sextw"(%[[v867]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v870:[0-9]+]] = "riscv.slt"(%[[v868]], %[[v869]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v871:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v870]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v258:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v871]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v258]]) [^[[bb38:[0-9]+]], ^[[bb39:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb38]]():
// CHECK-NEXT:         %[[v863:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v255]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v864:[0-9]+]] = "riscv.sextw"(%[[v863]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v861:[0-9]+]] = "riscv.sh2add"(%[[v864]], %[[varg7_1]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v857:[0-9]+]] = "riscv.lw"(%[[v861]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v858:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v857]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v854:[0-9]+]] = "riscv.sh2add"(%[[v864]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v850:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v858]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v854]], %[[v850]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb46:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb46]]():
// CHECK-NEXT:         %[[v845:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v255]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v846:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v887]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v847:[0-9]+]] = "riscv.addw"(%[[v846]], %[[v845]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v848:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v847]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v251:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v848]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v251]]) [^[[bb35]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb39]]():
// CHECK-NEXT:         %[[v264:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v923]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v264]]) [^[[bb50:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb50]](%[[varg50_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v266:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg50_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v839:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v266]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v840:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v921]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v841:[0-9]+]] = "riscv.sextw"(%[[v839]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v842:[0-9]+]] = "riscv.sextw"(%[[v840]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v843:[0-9]+]] = "riscv.slt"(%[[v841]], %[[v842]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v844:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v843]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v267:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v844]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v267]]) [^[[bb53:[0-9]+]], ^[[bb54:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb53]]():
// CHECK-NEXT:         %[[v835:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v266]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v836:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v885]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v837:[0-9]+]] = "riscv.subw"(%[[v835]], %[[v836]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v838:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v837]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v832:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v838]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v833:[0-9]+]] = "riscv.sextw"(%[[v832]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v830:[0-9]+]] = "riscv.sh2add"(%[[v833]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v826:[0-9]+]] = "riscv.lw"(%[[v830]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v827:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v826]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v821:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v827]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v822:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v883]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v823:[0-9]+]] = "riscv.srlw"(%[[v821]], %[[v822]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v824:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v823]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v817:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v818:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v883]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v819:[0-9]+]] = "riscv.subw"(%[[v817]], %[[v818]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v820:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v819]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v813:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v827]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v814:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v820]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v815:[0-9]+]] = "riscv.sllw"(%[[v813]], %[[v814]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v816:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v815]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v809:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v824]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v810:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v816]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v811:[0-9]+]] = "riscv.or"(%[[v810]], %[[v809]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v812:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v811]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v807:[0-9]+]] = "riscv.sh2add"(%[[v833]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v803:[0-9]+]] = "riscv.lw"(%[[v807]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v804:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v803]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v798:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v804]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v799:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v800:[0-9]+]] = "riscv.srlw"(%[[v798]], %[[v799]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v801:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v800]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v794:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v795:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v881]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v796:[0-9]+]] = "riscv.subw"(%[[v794]], %[[v795]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v797:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v796]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v790:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v804]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v791:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v797]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v792:[0-9]+]] = "riscv.sllw"(%[[v790]], %[[v791]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v793:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v792]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v786:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v801]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v787:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v793]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v788:[0-9]+]] = "riscv.or"(%[[v787]], %[[v786]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v789:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v788]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v782:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v812]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v783:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v789]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v784:[0-9]+]] = "riscv.xor"(%[[v783]], %[[v782]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v785:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v784]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v780:[0-9]+]] = "riscv.sh2add"(%[[v833]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v776:[0-9]+]] = "riscv.lw"(%[[v780]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v777:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v776]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v771:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v777]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v772:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v879]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v773:[0-9]+]] = "riscv.srlw"(%[[v771]], %[[v772]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v774:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v773]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v767:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v785]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v768:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v774]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v769:[0-9]+]] = "riscv.xor"(%[[v768]], %[[v767]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v770:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v769]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v763:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v266]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v764:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v893]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v765:[0-9]+]] = "riscv.subw"(%[[v763]], %[[v764]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v766:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v765]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v760:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v766]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v761:[0-9]+]] = "riscv.sextw"(%[[v760]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v758:[0-9]+]] = "riscv.sh2add"(%[[v761]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v754:[0-9]+]] = "riscv.lw"(%[[v758]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v755:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v754]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v749:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v755]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v750:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v877]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v751:[0-9]+]] = "riscv.srlw"(%[[v749]], %[[v750]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v752:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v751]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v745:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v746:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v877]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v747:[0-9]+]] = "riscv.subw"(%[[v745]], %[[v746]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v748:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v747]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v741:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v755]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v742:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v748]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v743:[0-9]+]] = "riscv.sllw"(%[[v741]], %[[v742]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v744:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v743]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v737:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v752]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v738:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v744]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v739:[0-9]+]] = "riscv.or"(%[[v738]], %[[v737]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v740:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v739]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v735:[0-9]+]] = "riscv.sh2add"(%[[v761]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v731:[0-9]+]] = "riscv.lw"(%[[v735]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v732:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v731]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v726:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v732]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v727:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v875]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v728:[0-9]+]] = "riscv.srlw"(%[[v726]], %[[v727]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v729:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v728]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v722:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v723:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v875]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v724:[0-9]+]] = "riscv.subw"(%[[v722]], %[[v723]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v725:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v724]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v718:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v732]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v719:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v725]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v720:[0-9]+]] = "riscv.sllw"(%[[v718]], %[[v719]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v721:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v720]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v714:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v729]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v715:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v721]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v716:[0-9]+]] = "riscv.or"(%[[v715]], %[[v714]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v717:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v716]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v710:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v740]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v711:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v717]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v712:[0-9]+]] = "riscv.xor"(%[[v711]], %[[v710]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v713:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v712]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v708:[0-9]+]] = "riscv.sh2add"(%[[v761]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v704:[0-9]+]] = "riscv.lw"(%[[v708]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v705:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v704]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v699:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v705]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v700:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v873]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v701:[0-9]+]] = "riscv.srlw"(%[[v699]], %[[v700]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v702:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v701]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v695:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v713]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v696:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v702]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v697:[0-9]+]] = "riscv.xor"(%[[v696]], %[[v695]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v698:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v697]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v691:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v266]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v692:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v923]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v693:[0-9]+]] = "riscv.subw"(%[[v691]], %[[v692]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v694:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v693]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v688:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v694]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v689:[0-9]+]] = "riscv.sextw"(%[[v688]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v686:[0-9]+]] = "riscv.sh2add"(%[[v689]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v682:[0-9]+]] = "riscv.lw"(%[[v686]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v683:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v682]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v677:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v683]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v678:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v770]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v679:[0-9]+]] = "riscv.addw"(%[[v678]], %[[v677]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v680:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v679]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v673:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v266]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v674:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v883]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v675:[0-9]+]] = "riscv.subw"(%[[v673]], %[[v674]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v676:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v675]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v670:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v676]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v671:[0-9]+]] = "riscv.sextw"(%[[v670]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v668:[0-9]+]] = "riscv.sh2add"(%[[v671]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v664:[0-9]+]] = "riscv.lw"(%[[v668]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v665:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v664]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v659:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v680]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v660:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v665]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v661:[0-9]+]] = "riscv.addw"(%[[v660]], %[[v659]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v662:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v661]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v655:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v662]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v656:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v698]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v657:[0-9]+]] = "riscv.addw"(%[[v656]], %[[v655]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v658:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v657]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v652:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v266]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v653:[0-9]+]] = "riscv.sextw"(%[[v652]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v650:[0-9]+]] = "riscv.sh2add"(%[[v653]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v646:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v658]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v650]], %[[v646]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb108:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb108]]():
// CHECK-NEXT:         %[[v641:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v266]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v642:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v887]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v643:[0-9]+]] = "riscv.addw"(%[[v642]], %[[v641]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v644:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v643]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v262:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v644]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v262]]) [^[[bb50]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb54]]():
// CHECK-NEXT:         %[[v639:[0-9]+]] = "riscv.sh2add"(%[[v918]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v635:[0-9]+]] = "riscv.lw"(%[[v639]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v636:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v635]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v632:[0-9]+]] = "riscv.sh2add"(%[[v916]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v628:[0-9]+]] = "riscv.lw"(%[[v632]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v629:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v628]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v625:[0-9]+]] = "riscv.sh2add"(%[[v914]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v621:[0-9]+]] = "riscv.lw"(%[[v625]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v622:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v621]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v618:[0-9]+]] = "riscv.sh2add"(%[[v912]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v614:[0-9]+]] = "riscv.lw"(%[[v618]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v615:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v614]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v611:[0-9]+]] = "riscv.sh2add"(%[[v910]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v607:[0-9]+]] = "riscv.lw"(%[[v611]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v608:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v607]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v604:[0-9]+]] = "riscv.sh2add"(%[[v908]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v600:[0-9]+]] = "riscv.lw"(%[[v604]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v601:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v600]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v597:[0-9]+]] = "riscv.sh2add"(%[[v906]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v593:[0-9]+]] = "riscv.lw"(%[[v597]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v594:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v593]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v590:[0-9]+]] = "riscv.sh2add"(%[[v904]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v586:[0-9]+]] = "riscv.lw"(%[[v590]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v587:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v586]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v232:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v608]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v233:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v601]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v234:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v594]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v235:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v587]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v236:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v925]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v237:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v615]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v238:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v622]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v239:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v629]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v240:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v636]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v232]], %[[v233]], %[[v234]], %[[v235]], %[[v236]], %[[v237]], %[[v238]], %[[v239]], %[[v240]]) [^[[bb128:[0-9]+]]] : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb128]](%[[varg128_0:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg128_1:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg128_2:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg128_3:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg128_4:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg128_5:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg128_6:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg128_7:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg128_8:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v250:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_8]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v249:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_7]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v248:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_6]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v247:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_5]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v246:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_4]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v245:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_3]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v244:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_2]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v243:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_1]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v242:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg128_0]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v579:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v246]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v580:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v921]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v581:[0-9]+]] = "riscv.sextw"(%[[v579]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v582:[0-9]+]] = "riscv.sextw"(%[[v580]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v583:[0-9]+]] = "riscv.slt"(%[[v581]], %[[v582]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v584:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v583]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v256:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v584]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v256]]) [^[[bb131:[0-9]+]], ^[[bb132:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb131]]():
// CHECK-NEXT:         %[[v575:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v576:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v903]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v577:[0-9]+]] = "riscv.srlw"(%[[v575]], %[[v576]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v578:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v577]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v571:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v572:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v903]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v573:[0-9]+]] = "riscv.subw"(%[[v571]], %[[v572]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v574:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v573]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v567:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v568:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v574]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v569:[0-9]+]] = "riscv.sllw"(%[[v567]], %[[v568]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v570:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v569]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v563:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v578]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v564:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v570]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v565:[0-9]+]] = "riscv.or"(%[[v564]], %[[v563]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v566:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v565]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v559:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v560:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v899]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v561:[0-9]+]] = "riscv.srlw"(%[[v559]], %[[v560]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v562:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v561]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v555:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v556:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v899]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v557:[0-9]+]] = "riscv.subw"(%[[v555]], %[[v556]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v558:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v557]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v551:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v552:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v558]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v553:[0-9]+]] = "riscv.sllw"(%[[v551]], %[[v552]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v554:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v553]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v547:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v562]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v548:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v554]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v549:[0-9]+]] = "riscv.or"(%[[v548]], %[[v547]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v550:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v549]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v543:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v566]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v544:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v550]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v545:[0-9]+]] = "riscv.xor"(%[[v544]], %[[v543]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v546:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v545]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v539:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v540:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v897]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v541:[0-9]+]] = "riscv.srlw"(%[[v539]], %[[v540]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v542:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v541]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v535:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v536:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v897]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v537:[0-9]+]] = "riscv.subw"(%[[v535]], %[[v536]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v538:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v537]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v531:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v532:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v538]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v533:[0-9]+]] = "riscv.sllw"(%[[v531]], %[[v532]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v534:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v533]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v527:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v542]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v528:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v534]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v529:[0-9]+]] = "riscv.or"(%[[v528]], %[[v527]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v530:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v529]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v523:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v546]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v524:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v530]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v525:[0-9]+]] = "riscv.xor"(%[[v524]], %[[v523]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v526:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v525]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v519:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v520:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v243]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v521:[0-9]+]] = "riscv.and"(%[[v520]], %[[v519]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v522:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v521]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v515:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v516:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v895]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v517:[0-9]+]] = "riscv.xor"(%[[v516]], %[[v515]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v518:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v517]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v511:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v518]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v512:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v244]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v513:[0-9]+]] = "riscv.and"(%[[v512]], %[[v511]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v514:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v513]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v507:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v522]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v508:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v514]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v509:[0-9]+]] = "riscv.xor"(%[[v508]], %[[v507]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v510:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v509]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v503:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v245]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v504:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v526]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v505:[0-9]+]] = "riscv.addw"(%[[v504]], %[[v503]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v506:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v505]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v499:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v506]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v500:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v510]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v501:[0-9]+]] = "riscv.addw"(%[[v500]], %[[v499]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v502:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v501]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v496:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v246]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v497:[0-9]+]] = "riscv.sextw"(%[[v496]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v494:[0-9]+]] = "riscv.sh2add"(%[[v497]], %[[varg7_2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v490:[0-9]+]] = "riscv.lw"(%[[v494]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v491:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v490]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v485:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v502]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v486:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v491]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v487:[0-9]+]] = "riscv.addw"(%[[v486]], %[[v485]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v488:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v487]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v483:[0-9]+]] = "riscv.sh2add"(%[[v497]], %[[varg7_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v479:[0-9]+]] = "riscv.lw"(%[[v483]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v480:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v479]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v474:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v488]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v475:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v480]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v476:[0-9]+]] = "riscv.addw"(%[[v475]], %[[v474]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v477:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v476]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v470:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v471:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v893]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v472:[0-9]+]] = "riscv.srlw"(%[[v470]], %[[v471]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v473:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v472]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v466:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v467:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v893]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v468:[0-9]+]] = "riscv.subw"(%[[v466]], %[[v467]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v469:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v468]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v462:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v463:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v469]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v464:[0-9]+]] = "riscv.sllw"(%[[v462]], %[[v463]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v465:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v464]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v458:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v473]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v459:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v465]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v460:[0-9]+]] = "riscv.or"(%[[v459]], %[[v458]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v461:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v460]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v454:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v455:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v891]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v456:[0-9]+]] = "riscv.srlw"(%[[v454]], %[[v455]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v457:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v456]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v450:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v451:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v891]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v452:[0-9]+]] = "riscv.subw"(%[[v450]], %[[v451]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v453:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v452]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v446:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v447:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v453]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v448:[0-9]+]] = "riscv.sllw"(%[[v446]], %[[v447]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v449:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v448]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v442:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v457]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v443:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v449]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v444:[0-9]+]] = "riscv.or"(%[[v443]], %[[v442]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v445:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v444]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v438:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v461]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v439:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v445]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v440:[0-9]+]] = "riscv.xor"(%[[v439]], %[[v438]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v441:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v440]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v434:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v435:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v889]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v436:[0-9]+]] = "riscv.srlw"(%[[v434]], %[[v435]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v437:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v436]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v430:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v901]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v431:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v889]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v432:[0-9]+]] = "riscv.subw"(%[[v430]], %[[v431]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v433:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v432]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v426:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v427:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v433]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v428:[0-9]+]] = "riscv.sllw"(%[[v426]], %[[v427]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v429:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v428]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v422:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v437]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v423:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v429]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v424:[0-9]+]] = "riscv.or"(%[[v423]], %[[v422]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v425:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v424]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v418:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v441]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v419:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v425]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v420:[0-9]+]] = "riscv.xor"(%[[v419]], %[[v418]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v421:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v420]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v414:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v415:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v249]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v416:[0-9]+]] = "riscv.and"(%[[v415]], %[[v414]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v417:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v416]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v410:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v411:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v248]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v412:[0-9]+]] = "riscv.and"(%[[v411]], %[[v410]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v413:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v412]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v406:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v417]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v407:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v413]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v408:[0-9]+]] = "riscv.xor"(%[[v407]], %[[v406]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v409:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v408]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v402:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v249]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v403:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v248]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v404:[0-9]+]] = "riscv.and"(%[[v403]], %[[v402]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v405:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v404]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v398:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v409]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v399:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v405]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v400:[0-9]+]] = "riscv.xor"(%[[v399]], %[[v398]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v401:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v400]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v394:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v421]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v395:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v401]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v396:[0-9]+]] = "riscv.addw"(%[[v395]], %[[v394]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v397:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v396]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v390:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v247]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v391:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v477]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v392:[0-9]+]] = "riscv.addw"(%[[v391]], %[[v390]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v393:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v392]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v386:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v477]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v387:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v397]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v388:[0-9]+]] = "riscv.addw"(%[[v387]], %[[v386]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v389:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v388]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb183:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb183]]():
// CHECK-NEXT:         %[[v382:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v246]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v383:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v887]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v384:[0-9]+]] = "riscv.addw"(%[[v383]], %[[v382]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v385:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v384]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v222:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v393]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v223:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v224:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v243]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v225:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v244]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v226:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v385]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v227:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v248]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v228:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v249]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v229:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v230:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v389]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v222]], %[[v223]], %[[v224]], %[[v225]], %[[v226]], %[[v227]], %[[v228]], %[[v229]], %[[v230]]) [^[[bb128]]] : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb132]]():
// CHECK-NEXT:         %[[v380:[0-9]+]] = "riscv.sh2add"(%[[v918]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v376:[0-9]+]] = "riscv.lw"(%[[v380]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v377:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v376]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v371:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v377]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v372:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v250]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v373:[0-9]+]] = "riscv.addw"(%[[v372]], %[[v371]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v374:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v373]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v369:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v374]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v380]], %[[v369]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v366:[0-9]+]] = "riscv.sh2add"(%[[v916]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v362:[0-9]+]] = "riscv.lw"(%[[v366]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v363:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v362]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v357:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v363]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v358:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v249]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v359:[0-9]+]] = "riscv.addw"(%[[v358]], %[[v357]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v360:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v359]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v355:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v360]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v366]], %[[v355]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v352:[0-9]+]] = "riscv.sh2add"(%[[v914]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v348:[0-9]+]] = "riscv.lw"(%[[v352]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v349:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v348]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v343:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v349]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v344:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v248]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v345:[0-9]+]] = "riscv.addw"(%[[v344]], %[[v343]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v346:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v345]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v341:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v346]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v352]], %[[v341]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v338:[0-9]+]] = "riscv.sh2add"(%[[v912]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v334:[0-9]+]] = "riscv.lw"(%[[v338]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v335:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v334]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v329:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v335]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v330:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v247]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v331:[0-9]+]] = "riscv.addw"(%[[v330]], %[[v329]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v332:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v331]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v327:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v332]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v338]], %[[v327]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v324:[0-9]+]] = "riscv.sh2add"(%[[v910]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v320:[0-9]+]] = "riscv.lw"(%[[v324]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v321:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v320]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v315:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v321]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v316:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v242]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v317:[0-9]+]] = "riscv.addw"(%[[v316]], %[[v315]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v318:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v317]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v313:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v318]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v324]], %[[v313]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v310:[0-9]+]] = "riscv.sh2add"(%[[v908]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v306:[0-9]+]] = "riscv.lw"(%[[v310]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v307:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v306]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v301:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v307]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v302:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v243]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v303:[0-9]+]] = "riscv.addw"(%[[v302]], %[[v301]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v304:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v303]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v299:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v304]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v310]], %[[v299]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v296:[0-9]+]] = "riscv.sh2add"(%[[v906]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v292:[0-9]+]] = "riscv.lw"(%[[v296]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v293:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v292]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v287:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v293]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v288:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v244]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v289:[0-9]+]] = "riscv.addw"(%[[v288]], %[[v287]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v290:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v289]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v285:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v290]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v296]], %[[v285]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v282:[0-9]+]] = "riscv.sh2add"(%[[v904]], %[[varg7_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v278:[0-9]+]] = "riscv.lw"(%[[v282]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v279:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v278]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v273:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v279]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v274:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v245]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         %[[v275:[0-9]+]] = "riscv.addw"(%[[v274]], %[[v273]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v276:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v275]]) : (!riscv.reg) -> i32
// CHECK-NEXT:         %[[v271:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v276]]) : (i32) -> !riscv.reg
// CHECK-NEXT:         "riscv.sw"(%[[v282]], %[[v271]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()
