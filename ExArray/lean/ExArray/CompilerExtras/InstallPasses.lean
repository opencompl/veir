module
public meta import Lean.Compiler.LCNF.PassManager
public meta import ExArray.CompilerExtras.ReduceArity
public meta import ExArray.CompilerExtras.ConstrJpDestr

public import Lean

@[cpass]
public meta def installExArrayPasses : Lean.Compiler.LCNF.PassInstaller where
  phase := .mono
  install passes := do
    let mut res := #[]
    for pass in passes do
      if pass.name = `reduceArity then
        res := res.push Lean.Compiler.LCNF.Extras.removeSpuriousConstr
        res := res.push Lean.Compiler.LCNF.Extras.reduceArity
      else
        res := res.push pass
    pure res
