// RUN: not veir-opt %s --split-input-file --allow-unregistered-dialect -p=register-allocation-riscv64 2>&1 >/dev/null | filecheck %s

// Every shape the pass rejects, one per chunk. A failing chunk does not stop the
// following ones, so all the diagnostics below are produced in a single run.
//
// The pass reports no source location, so a message is tied to its chunk only by
// position: the CHECK lines at the bottom are in chunk order and must stay that way.

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

// -----

// A function entry block with arguments.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg) -> ()}> ({
  ^entry(%a : !riscv.reg):
    %sum = "riscv.add"(%a, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

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

// -----

// A function with return values.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"(%a) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

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

// CHECK:      register allocation expects a module with a single region
// CHECK:      register allocation expects a module body with a single block
// CHECK:      register allocation does not support block arguments
// CHECK:      register allocation does not support block arguments
// CHECK:      register allocation requires a single-block function
// CHECK:      register allocation does not support function return values
// CHECK:      register allocation does not support operations with nested regions
// CHECK:      register allocation requires a single-block function
// CHECK-NOT:  error
