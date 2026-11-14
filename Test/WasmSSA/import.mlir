"builtin.module"() ({
  "wasmssa.import_func"() <{importName = "foo", moduleName = "my_module", sym_name = "func_0", type = (i32) -> ()}> : () -> ()
  "wasmssa.import_func"() <{importName = "bar", moduleName = "my_module", sym_name = "func_1", type = (i32) -> ()}> : () -> ()
  "wasmssa.import_table"() <{importName = "table", moduleName = "my_module", sym_name = "table_0", type = !wasmssa<tabletype !wasmssa.funcref [2:]>}> : () -> ()
  "wasmssa.import_mem"() <{importName = "mem", limits = !wasmssa<limit[2:]>, moduleName = "my_module", sym_name = "mem_0"}> : () -> ()
  "wasmssa.import_global"() <{importName = "glob", moduleName = "my_module", sym_name = "global_0", type = i32}> : () -> ()
  "wasmssa.import_global"() <{importName = "glob_mut", isMutable, moduleName = "my_other_module", sym_name = "global_1", type = i32}> : () -> ()
}) : () -> ()
