module

public import Lean

open Lean

public meta initialize opCodesExt : TagDeclarationExtension ← mkTagDeclarationExtension

syntax (name := dialect_name) "dialect_name" ppSpace str : attr

public meta initialize dialectNameAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `dialect_name
    descr := "Override the MLIR mnemonic for a VeIR dialect opcode definition."
    getParam := fun _ => fun
      | `(attr| dialect_name $name:str) => pure name.getString
      | _ => Elab.throwUnsupportedSyntax
  }

meta initialize registerBuiltinAttribute {
  name := `opcodes
  descr := "Register an inductive type as a VeIR dialect opcode definition."
  applicationTime := .afterCompilation
  add := λ decl stx attrKind => do
    setEnv <| opCodesExt.tag (← getEnv) decl
}
