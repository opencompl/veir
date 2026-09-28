module

public import Veir.Interpreter.Basic
public import Veir.Dialects.LLVM.Interpreter

public section

open CTree

namespace Veir.CTreeInterpreter

/-- SSA requests contain pointers and individual runtime values, never a variable
store. The context index prevents running a tree against a different IR. -/
inductive SSAIn (ctx : WfIRContext OpCode) where
  | readOperands (op : OperationPtr)
  | writeResults (op : OperationPtr) (values : Array RuntimeValue)
  | writeArguments (block : BlockPtr) (values : Array RuntimeValue)
  /-- An inherited region scope or a fresh function scope. -/
  | enterScope (inherit : Bool)
  | leaveScope

@[expose]
def SSAE (ctx : WfIRContext OpCode) : SSAIn ctx → Type
  | .readOperands _ => Array RuntimeValue
  | .writeResults _ _ | .writeArguments _ _ | .enterScope _ | .leaveScope => Unit

/-- Pure semantics with explicit SSA effects. Only the concrete handler owns the
variable store; LLVM freeze, failure, and undefined behavior remain effects. -/
abbrev Tree (ctx : WfIRContext OpCode) (α : Type) :=
  CTree (SSAE ctx ⊕ₑ ErrorE ⊕ₑ UBE) FreezeC α

end Veir.CTreeInterpreter
