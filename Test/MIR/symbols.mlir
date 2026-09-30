// RUN: veir2mir %s | filecheck %s

// References use raw MLIR spelling; definitions contain decoded string bytes.
// Quoted and escaped references must resolve to the same function, and LLVM
// identifiers and YAML scalars need their own escaping.
"builtin.module"() ({
  "func.func"() <{sym_name = "caller", function_type = () -> ()}> ({
    "riscv_cf.call"() <{callee = @"leaf"}> : () -> ()
    "riscv_cf.call"() <{callee = @"le\61f"}> : () -> ()
    "riscv_cf.call"() <{callee = @"name with spaces"}> : () -> ()
    "riscv_cf.call"() <{callee = @"name: # 'quoted'"}> : () -> ()
    "riscv_cf.call"() <{callee = @"quote\"slash\\line\n\t\01"}> : () -> ()
    "riscv_cf.call"() <{callee = @"123"}> : () -> ()
    "riscv_cf.call"() <{callee = @"caf\C3\A9"}> : () -> ()
    "riscv_cf.call"() <{callee = @"external name"}> : () -> ()
    "riscv_cf.call"() <{callee = @"external\20name"}> : () -> ()
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "leaf", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "name with spaces", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "name: # 'quoted'", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "quote\"slash\\line\n\t\01", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "123", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "café", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// Definitions use LLVM's \HH escapes, even for quotes and backslashes.
// CHECK: define i64 @caller()
// CHECK: define i64 @leaf()
// CHECK: define i64 @"name with spaces"()
// CHECK: define i64 @"name: # 'quoted'"()
// CHECK: define i64 @"quote\22slash\5Cline\0A\09\01"()
// CHECK: define i64 @"123"()
// CHECK: define i64 @"caf\C3\A9"()
// CHECK-NEXT: ret i64 0
// CHECK-NEXT: }
// Only one declaration, and none for locally defined functions.
// CHECK-NEXT: declare void @"external name"()
// CHECK-NEXT: attributes #0 =

// Calls carry the relocation flag and use the same canonical LLVM identifiers.
// CHECK-LABEL: name: caller
// CHECK: PseudoCALL target-flags(riscv-call) @leaf,
// CHECK: PseudoCALL target-flags(riscv-call) @leaf,
// CHECK: PseudoCALL target-flags(riscv-call) @"name with spaces",
// CHECK: PseudoCALL target-flags(riscv-call) @"name: # 'quoted'",
// CHECK: PseudoCALL target-flags(riscv-call) @"quote\22slash\5Cline\0A\09\01",
// CHECK: PseudoCALL target-flags(riscv-call) @"123",
// CHECK: PseudoCALL target-flags(riscv-call) @"caf\C3\A9",
// CHECK: PseudoCALL target-flags(riscv-call) @"external name",
// CHECK: PseudoCALL target-flags(riscv-call) @"external name",

// YAML uses double-quote/backslash escapes and \xHH for control characters.
// CHECK-LABEL: name: leaf
// CHECK-LABEL: name: "name with spaces"
// CHECK-LABEL: name: "name: # 'quoted'"
// CHECK-LABEL: name: "quote\"slash\\line\x0A\x09\x01"
// CHECK-LABEL: name: "123"
// CHECK-LABEL: name: "café"
