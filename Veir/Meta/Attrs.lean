module 

public import Lean

open Lean

public meta initialize opCodesExt : TagDeclarationExtension ← mkTagDeclarationExtension 

meta initialize registerBuiltinAttribute {
  name := `opcodes
  descr := "Register an inductive type as a VeIR dialect opcode definition."
  applicationTime := .afterCompilation
  add := λ decl stx attrKind => do
    setEnv <| opCodesExt.tag (← getEnv) decl
}
