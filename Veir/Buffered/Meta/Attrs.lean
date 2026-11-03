module

public import Lean

open Lean

public meta initialize bufferedOpCodesExt : TagDeclarationExtension ← mkTagDeclarationExtension

meta initialize registerBuiltinAttribute {
  name := `buffered_opcodes
  descr := "Register an inductive type as a VeIR dialect opcode definition."
  applicationTime := .afterCompilation
  add := λ decl stx attrKind => do
    setEnv <| bufferedOpCodesExt.tag (← getEnv) decl
}
