// RUN: veir-opt %s --print-op-generic -p=register-precolouring-riscv64,register-allocation-riscv64 | filecheck %s

// The register passes in pipeline order. Precolouring pins argument i to a<i> and copies it into
// a fresh value, and copies result i into its return value in a<i>. Allocation then gives every
// remaining value a virtual register; the precoloured values keep theirs.
//
// The only physical register the pipeline assigns before precolouring is x0.

"builtin.module"() ({
  // Non-function operations and declarations are passed over.
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64,
    global_type = i32, linkage = #llvm.linkage<external>, sym_name = "global",
    value = 41 : i32}> ({}) : () -> ()

  // CHECK-LABEL: "llvm.mlir.global"()
  // CHECK-SAME:  "sym_name" = "global"

  "riscv_cf.func"() <{sym_name = "external", function_type = (!riscv.reg) -> !riscv.reg}> ({}) : () -> ()

  // CHECK-LABEL: "function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "external"}> ({}) : () -> ()

  "riscv_cf.func"() <{sym_name = "return_only", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "return_only"
  // CHECK-NEXT:  ^{{[^ ]+}}():
  // CHECK-NEXT:  "riscv_cf.return"() : () -> ()

  // Virtual registers are reused once a value dies, and numbering restarts at j0 in each function.
  "riscv_cf.func"() <{sym_name = "arithmetic", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    %sum = "riscv.add"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "arithmetic"
  // CHECK-NEXT:  ^{{[^ ]+}}():
  // CHECK-NEXT:  [[A:%[^ ]+]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg<j0>
  // CHECK-NEXT:  [[B:%[^ ]+]] = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg<j1>
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[A]], [[B]]) : (!riscv.reg<j0>, !riscv.reg<j1>) -> !riscv.reg<j0>
  // CHECK-NEXT:  "riscv_cf.return"() : () -> ()

  // A fixed x0 is left alone.
  "riscv_cf.func"() <{sym_name = "fixed_zero", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    %zero = "rv64.get_register"() : () -> !riscv.reg<x0>
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "fixed_zero"
  // CHECK-NEXT:  ^{{[^ ]+}}():
  // CHECK-NEXT:  "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg<j0>
  // CHECK-NEXT:  "rv64.get_register"() : () -> !riscv.reg<x0>
  // CHECK-NEXT:  "riscv_cf.return"() : () -> ()

  // Argument i is pinned to a<i> and copied into a fresh value; an unused argument is pinned
  // but not copied. The result is copied into its return value in a0. The signature follows
  // the arguments and its result type stays unassigned.
  "riscv_cf.func"() <{sym_name = "args_and_result", function_type = (!riscv.reg, !riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^entry(%a : !riscv.reg, %unused : !riscv.reg, %b : !riscv.reg):
    %s = "riscv.add"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %t = "riscv.add"(%s, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"(%t) : (!riscv.reg) -> ()
  }) : () -> ()

  // CHECK-LABEL: "function_type" = (!riscv.reg<x10>, !riscv.reg<x11>, !riscv.reg<x12>) -> !riscv.reg, "sym_name" = "args_and_result"
  // CHECK-NEXT:  ^{{[^ ]+}}([[A:%[^ ]+]] : !riscv.reg<x10>, %{{[^ ]+}} : !riscv.reg<x11>, [[B:%[^ ]+]] : !riscv.reg<x12>):
  // CHECK-NEXT:  [[CA:%[^ ]+]] = "riscv.mv"([[A]]) : (!riscv.reg<x10>) -> !riscv.reg<j1>
  // CHECK-NEXT:  [[CB:%[^ ]+]] = "riscv.mv"([[B]]) : (!riscv.reg<x12>) -> !riscv.reg<j0>
  // CHECK-NEXT:  [[S:%[^ ]+]] = "riscv.add"([[CA]], [[CB]]) : (!riscv.reg<j1>, !riscv.reg<j0>) -> !riscv.reg<j0>
  // CHECK-NEXT:  [[T:%[^ ]+]] = "riscv.add"([[S]], [[CA]]) : (!riscv.reg<j0>, !riscv.reg<j1>) -> !riscv.reg<j0>
  // CHECK-NEXT:  [[R:%[^ ]+]] = "riscv.mv"([[T]]) : (!riscv.reg<j0>) -> !riscv.reg<x10>
  // CHECK-NEXT:  "riscv_cf.return"([[R]]) : (!riscv.reg<x10>) -> ()

  // A result preallocated to x0 is copied into its return value.
  "riscv_cf.func"() <{sym_name = "return_zero", function_type = () -> !riscv.reg}> ({
    %z = "rv64.get_register"() : () -> !riscv.reg<x0>
    "riscv_cf.return"(%z) : (!riscv.reg<x0>) -> ()
  }) : () -> ()

  // CHECK-LABEL: "function_type" = () -> !riscv.reg, "sym_name" = "return_zero"
  // CHECK-NEXT:  ^{{[^ ]+}}():
  // CHECK-NEXT:  [[Z:%[^ ]+]] = "rv64.get_register"() : () -> !riscv.reg<x0>
  // CHECK-NEXT:  [[R:%[^ ]+]] = "riscv.mv"([[Z]]) : (!riscv.reg<x0>) -> !riscv.reg<x10>
  // CHECK-NEXT:  "riscv_cf.return"([[R]]) : (!riscv.reg<x10>) -> ()

  // Returning one value twice copies it twice.
  "riscv_cf.func"() <{sym_name = "same_value_twice", function_type = () -> (!riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"(%a, %a) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

  // CHECK-LABEL: "function_type" = () -> (!riscv.reg, !riscv.reg), "sym_name" = "same_value_twice"
  // CHECK-NEXT:  ^{{[^ ]+}}():
  // CHECK-NEXT:  [[A:%[^ ]+]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg<j0>
  // CHECK-NEXT:  [[R0:%[^ ]+]] = "riscv.mv"([[A]]) : (!riscv.reg<j0>) -> !riscv.reg<x10>
  // CHECK-NEXT:  [[R1:%[^ ]+]] = "riscv.mv"([[A]]) : (!riscv.reg<j0>) -> !riscv.reg<x11>
  // CHECK-NEXT:  "riscv_cf.return"([[R0]], [[R1]]) : (!riscv.reg<x10>, !riscv.reg<x11>) -> ()

  // Arguments and return values already in their registers are kept.
  "riscv_cf.func"() <{sym_name = "already_precoloured", function_type = (!riscv.reg<x10>) -> (!riscv.reg, !riscv.reg)}> ({
  ^entry(%a : !riscv.reg<x10>):
    %c = "riscv.mv"(%a) : (!riscv.reg<x10>) -> !riscv.reg
    %d = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    %r0 = "riscv.mv"(%c) : (!riscv.reg) -> !riscv.reg<x10>
    %r1 = "riscv.mv"(%d) : (!riscv.reg) -> !riscv.reg<x11>
    "riscv_cf.return"(%r0, %r1) : (!riscv.reg<x10>, !riscv.reg<x11>) -> ()
  }) : () -> ()

  // CHECK-LABEL: "function_type" = (!riscv.reg<x10>) -> (!riscv.reg, !riscv.reg), "sym_name" = "already_precoloured"
  // CHECK-NEXT:  ^{{[^ ]+}}([[A:%[^ ]+]] : !riscv.reg<x10>):
  // CHECK-NEXT:  [[C:%[^ ]+]] = "riscv.mv"([[A]]) : (!riscv.reg<x10>) -> !riscv.reg<j1>
  // CHECK-NEXT:  [[D:%[^ ]+]] = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg<j0>
  // CHECK-NEXT:  [[R0:%[^ ]+]] = "riscv.mv"([[C]]) : (!riscv.reg<j1>) -> !riscv.reg<x10>
  // CHECK-NEXT:  [[R1:%[^ ]+]] = "riscv.mv"([[D]]) : (!riscv.reg<j0>) -> !riscv.reg<x11>
  // CHECK-NEXT:  "riscv_cf.return"([[R0]], [[R1]]) : (!riscv.reg<x10>, !riscv.reg<x11>) -> ()
}) : () -> ()
