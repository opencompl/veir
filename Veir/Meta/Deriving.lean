module

public meta import Lean.Elab.Deriving.Repr
public meta import Lean.Elab.Deriving.Hashable

/-!
Commands for deriving instances while sharing helpers between mutually recursive types.

Lean's standard Repr and Hashable handlers generate the whole mutual group's helpers
again for each requested instance. These commands accept types from a single mutual
group and generate its helpers once.
-/

namespace Veir

open Lean Elab Command Deriving

/--
Derive a class instance for a mutual group of types, generating helpers only once.

`className` is the name of the class to derive, `fnPrefix` is a prefix for the helper names (which
is useful for debugging), `mkHelpers` is a function that generates the helpers in a mutual block,
and `types` is the list of types to derive instances for.
-/
private meta def deriveSharedInstances (className : Name) (fnPrefix : String)
    (mkHelpers : Deriving.Context → TermElabM Syntax) (types : Array Syntax) : CommandElabM Unit := do
  /- Resolve the arguments as declaration names. -/
  let typeNames ← types.mapM resolveGlobalConstNoOverload
  let cmds ← liftTermElabM do
    /- Get the mutual group by fetching it from the first type. -/
    let ctx ← mkContext className fnPrefix typeNames[0]!
    /- Generate a `mutual ... end` syntax tree containing the helper functions. -/
    let helpers ← mkHelpers ctx
    /- The list of commands to be executed. -/
    let mut cmds : Array Lean.Command := #[⟨helpers⟩]

    /- For each type in the group, generate an instance using the generated helper. -/
    for typeName in typeNames do
      /- Sanity check that the user only provided types from the same mutual group. -/
      unless ctx.typeInfos.any (·.name == typeName) do
        throwError "{typeName} is not in the mutual group of {typeNames[0]!}"
      let instName ← mkInstName className typeName
      cmds := cmds ++ (← mkInstanceCmds { ctx with instName } className #[typeName])
    return cmds
  cmds.forM elabCommand

public section

/--
Derive Repr for distinct types from a single mutual group, generating helpers only once per type.
-/
elab "derive_mutual_repr " "for " types:ident,+ : command =>
  deriveSharedInstances ``Repr "repr" Repr.mkMutualBlock types.getElems

/--
Derive Hashable for distinct types from a single mutual group, generating helpers only once per
type.
-/
elab "derive_mutual_hashable " "for " types:ident,+ : command =>
  deriveSharedInstances ``Hashable "hash" Hashable.mkHashFuncs types.getElems

end

end Veir
