module

public meta import Lean

public import QPFTypes.Meta.QPFExpr.AddDecl
public import QPFTypes.Meta.QPFExpr.OfTypeExpr

/-!
# The `@[qpf]` attribute

Marking a type function definition `F` with `@[qpf]` shows that `F` is a QPF,
by building a `QPFExpr` from its definition (see `QPFExpr.ofTypeDef`),
and adding the corresponding declarations and instances to the environment
(see `QPFExpr.addDecls`).

The live parameters of `F` are those whose type is marked with `liveParam`.

`@[local qpf]` and `@[scoped qpf]` are supported, and register the generated
instances as local, resp. scoped, instances. The generated definitions
(e.g., `F.Uncurried`) are always added to the environment.
-/

public meta section

namespace QPFTypes
open Lean Meta Elab

initialize registerBuiltinAttribute {
  name := `qpf
  descr := "derive a QPF instance for a type function definition"
  applicationTime := .afterCompilation
  add := fun declName stx attrKind => do
    Attribute.Builtin.ensureNoArgs stx
    unless (← getConstInfo declName).isDefinition do
      throwError "@[qpf] can only be applied to definitions, but '{.ofConstName declName}' is not"
    MetaM.run' <|
      QPFExpr.ofTypeDef declName fun q levelParams deadVars =>
        q.addDecls declName levelParams (deadVars.map Expr.fvar) attrKind
  erase := fun declName =>
    throwError "@[qpf] cannot be erased from '{.ofConstName declName}'"
}

end QPFTypes
