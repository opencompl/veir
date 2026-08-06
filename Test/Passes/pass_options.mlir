// RUN: not veir-opt %s -p='mod-arith-to-arith{pow2-widht}' 2>&1 | filecheck %s --check-prefix=MISSPELLED
// RUN: not veir-opt %s -p='cse{whatever}' 2>&1 | filecheck %s --check-prefix=NO-OPTIONS
// RUN: not veir-opt %s -p='mod-arith{pow2-width}' 2>&1 | filecheck %s --check-prefix=GROUP
// RUN: not veir-opt %s -p='mod-arith-to-arith{pow2-width' 2>&1 | filecheck %s --check-prefix=UNCLOSED

// A pass name in a `-p` list may be followed by a brace-enclosed, space-separated list of
// boolean options; an option not named is off, and there is no `opt=value` form. These
// check the diagnostics for the ways that syntax can go wrong. That the options themselves
// take effect is covered by ModArithToArith/mul.mlir and
// FunctionBoundaryCoercion/mod_arith_pow2_width.mlir.

"builtin.module"() ({
}) : () -> ()

// MISSPELLED: pass 'mod-arith-to-arith' has no option 'pow2-widht' (it accepts: barrett, pow2-width)
// NO-OPTIONS: pass 'cse' has no option 'whatever' (it accepts no options)
// GROUP: pass group 'mod-arith' does not take options
// UNCLOSED: missing closing brace in the options of pass 'mod-arith-to-arith'
