// RUN: VEIR_ROUNDTRIP
// RUN: veir-opt %s --print-op-generic -p=canonicalize,cse,dce | filecheck %s
// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC
// RUN: veir2mir %s | filecheck %s --check-prefix=MIR

// Definitions and empty-region declarations both implement FunctionOpInterface.
// Function metadata survives parsing, printing, and ordinary optimization.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "external", function_type = (!riscv.reg) -> !riscv.reg, sym_visibility = "private"}> ({
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "pair", function_type = (!riscv.reg, !riscv.reg<x11>) -> (!riscv.reg, !riscv.reg<x11>), linkage = #llvm.linkage<internal>, CConv = #llvm.cconv<ccc>, arg_attrs = [{llvm.noundef}, {}]}> ({
  ^entry(%a: !riscv.reg, %b: !riscv.reg<x11>):
    "riscv_cf.return"(%a, %b) : (!riscv.reg, !riscv.reg<x11>) -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "caller", function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^entry(%a: !riscv.reg):
    %v = "riscv_cf.call"(%a) <{callee = @external}> : (!riscv.reg) -> !riscv.reg
    "riscv_cf.return"(%v) : (!riscv.reg) -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "void", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %v = "riscv.li"() <{value = 42 : i64}> : () -> !riscv.reg
    "riscv_cf.return"(%v) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "riscv_cf.func"() <{"function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "external", "sym_visibility" = "private"}> ({}) : () -> ()
// CHECK: "riscv_cf.func"() <{"CConv" = #llvm.cconv<ccc>, "arg_attrs" = [{llvm.noundef}, {}], "function_type" = (!riscv.reg, !riscv.reg<x11>) -> (!riscv.reg, !riscv.reg<x11>), "linkage" = #llvm.linkage<internal>, "sym_name" = "pair"}> ({
// CHECK: "riscv_cf.return"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg<x11>) -> ()
// CHECK: "riscv_cf.func"() <{"function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "caller"}> ({
// CHECK: "riscv_cf.call"(%{{.*}}) <{"callee" = @external}> : (!riscv.reg) -> !riscv.reg
// CHECK: "riscv_cf.func"() <{"function_type" = () -> (), "sym_name" = "void"}> ({
// CHECK: "riscv_cf.return"() : () -> ()
// CHECK: "riscv_cf.func"() <{"function_type" = () -> !riscv.reg, "sym_name" = "main"}> ({
// CHECK: "riscv_cf.return"(%{{.*}}) : (!riscv.reg) -> ()
// EXEC: Program output: #[0x000000000000002a#64]
// MIR: define i64 @pair(i64 %a0, i64 %a1)
// MIR: define i64 @caller(i64 %a0)
// MIR: define i64 @void()
// MIR: define i64 @main()
// MIR: declare void @external()
// MIR-LABEL: name: pair
// MIR: PseudoRET
// MIR-LABEL: name: caller
// MIR: PseudoCALL target-flags(riscv-call) @external
// MIR: PseudoRET
// MIR-LABEL: name: void
// MIR: PseudoRET
// MIR-LABEL: name: main
// MIR: PseudoRET
