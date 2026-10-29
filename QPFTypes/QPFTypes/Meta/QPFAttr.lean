module

public meta import Lean

public import QPFTypes.Meta.QPFExpr.AddDecl
public import QPFTypes.Meta.QPFExpr.OfTypeExpr
public import QPFTypes.Meta.QPFAttr.Cofix

/-!
# The `@[qpf]` attribute

Marking a type function definition `F` with `@[qpf]` shows that `F` is a QPF,
by building a `QPFExpr` from its definition (see `QPFExpr.ofTypeDef`),
and adding the corresponding declarations and instances to the environment
(see `QPFExpr.addDecls`).

The live parameters of `F` are those whose type is marked with `liveParam`.

Separately, `@[qpf]` may be applied to a coinductive type, i.e., a definition whose body is an
application of `Cofix`, in which case it defines the possibly-partial analogue `T.__partial`
of the type, via `CofixWithBot` (see `QPFTypes.Meta.QPFAttr.Cofix`).

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
    MetaM.run' do
      -- A coinductive type, rather than a (curried) type function: see `QPFAttr.Cofix`.
      if ← QPFAttr.isCofixDef declName then
        return ← QPFAttr.addPartialCofixType declName
      QPFExpr.ofTypeDef declName fun q levelParams deadVars =>
        q.addDecls declName levelParams (deadVars.map Expr.fvar) attrKind
  erase := fun declName =>
    throwError "@[qpf] cannot be erased from '{.ofConstName declName}'"
}

end QPFTypes
