// RUN: not veir-opt %s --split-input-file --allow-unregistered-dialect -p=register-precolouring-riscv64,register-allocation-riscv64 2>&1 >/dev/null | filecheck %s

// Every function shape the register passes reject, one per chunk. A failing chunk does not 
// stop the following ones, so all the diagnostics below are produced in a single run.

// The pass reads the functions out of the root's single region. A verified `builtin.module`
// always has exactly one, but the pipeline roots the pass at whatever operation it is given,
// and an unregistered operation makes no promise about its regions.
"test.outer"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}, {
  "riscv_cf.func"() <{sym_name = "g", function_type = () -> ()}> ({
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation expects a module with a single region

// -----

// The pass reads the functions out of the root's first block. A verified `builtin.module`
// body holds at most one, since its region is a graph region, but the graph-region rule
// exempts unregistered operations -- which is what the root may be.
"test.outer"() ({
^bb0:
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "cf.br"()[^bb1] : () -> ()
^bb1:
  "riscv_cf.func"() <{sym_name = "g", function_type = () -> ()}> ({
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "cf.br"()[^bb1] : () -> ()
}) : () -> ()

// CHECK:      register allocation expects a module body with a single block

// -----

// The module body is a single block that may still declare arguments: nothing can ever pass
// a value to them, since `verifyNoEntryBlockPredecessors` leaves a region's entry block
// without predecessors, but they exist as values the allocator never visits. The function
// here is well-formed, so only the module body's argument can be the cause.
"builtin.module"() ({
^body(%arg0 : !riscv.reg):
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation does not support block arguments

// -----

// A function with more arguments than the eight argument registers a0-a7: the ninth would
// be passed on the stack.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg, !riscv.reg, !riscv.reg,
      !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()}> ({
  ^entry(%a0 : !riscv.reg, %a1 : !riscv.reg, %a2 : !riscv.reg, %a3 : !riscv.reg,
         %a4 : !riscv.reg, %a5 : !riscv.reg, %a6 : !riscv.reg, %a7 : !riscv.reg,
         %a8 : !riscv.reg):
    %sum = "riscv.add"(%a0, %a8) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation supports at most 8 function arguments

// -----

// A function with more than one block.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
  ^entry:
    "riscv_cf.branch"()[^next] : () -> ()
  ^next:
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation requires a single-block function

// -----

// A function with three results: only a0 and a1 return values in registers.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"(%a, %a, %a) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation supports at most 2 function results

// -----

// A function that calls another: a value live across the call could be given a caller-saved
// register, which the call clobbers.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "g", function_type = () -> ()}> ({}) : () -> ()
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.call"() <{callee = @g}> : () -> ()
    %b = "riscv.add"(%a, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation does not support function calls

// -----

// A variadic function: its variadic arguments are not modeled.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!riscv.reg, ...)>, sym_name = "f"}> ({
  ^entry(%a : !riscv.reg):
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation does not support variadic functions

// -----

// The allocator only scans the ops of one block, so values defined in a nested region
// would silently keep their unallocated types.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    "test.container"() ({
      %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    }) : () -> ()
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation does not support operations with nested regions

// -----

// Every function is checked before any is rewritten: the later unsupported body must be
// rejected before allocation reaches the i32 value in the earlier one, which would fail
// with a different message.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "arith.constant"() <{value = 5 : i32}> : () -> i32
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "g", function_type = () -> ()}> ({
  ^entry:
    "riscv_cf.branch"()[^next] : () -> ()
  ^next:
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      register allocation requires a single-block function
// CHECK-NOT:  error
