module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.RISCV.Monotonicity
public import Veir.Interpreter.CTreePrimitiveRefinement
public import Veir.Dialects.RISCV.ResultsConform

import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Monotonicity of the RISC-V opcodes in CTrees

A RISC-V opcode runs its `Interp` semantics in CTrees, which is monotone in its operands and its
memory for every opcode but the loads. A load is left to `OpCode.interpretCTree_monotone_assumed`:
it reads the value bits of the bytes and drops their poison bits, so the source may read zeros
from bytes that nothing was stored to, where refined memory holds other bytes.
-/

open CTree

namespace Veir.CTree

/-- A RISC-V opcode runs its `Interp` semantics. -/
theorem interpretOp'_riscv (op : Riscv) (properties : propertiesOf (OpCode.riscv op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (regions : Array RegionPtr) :
    interpretOp' (.riscv op) properties resultTypes operands blockOperands mem regions =
      monadLift
        (Veir.interpretOp' (.riscv op) properties resultTypes operands blockOperands mem) := by
  rfl

/-- Every RISC-V opcode but the loads is monotone in CTrees. -/
theorem riscv_interpretOpTreeMonotone {op : Riscv} (h : op.isLoad = false) :
    InterpretOpTreeMonotone (.riscv op) :=
  have := riscv_interpretOp'ContextuallyMonotone h
  .of_lift (interpretOp'_riscv op)

/-- A refinement in `Interp` together with what holds of every result of the target. -/
private theorem Interp.isRefinedBy_and {R : α → β → Prop} {P : β → Prop} {s : Interp α}
    {t : Interp β} (h : Interp.isRefinedBy R s t) (hP : ∀ b, t = .ok b → P b) :
    Interp.isRefinedBy (fun a b => R a b ∧ P b) s t := by
  cases s <;> cases t <;> simp_all [Interp.isRefinedBy]

/--
A RISC-V opcode but a load is monotone in CTrees, with the results of the target of the types that
its `Interp` results have.
-/
theorem riscv_sim_typed {op : Riscv} {opType : OpCode} (hType : opType = .riscv op)
    (hLoad : op.isLoad = false) (properties : propertiesOf opType) (resultTypes types : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem')
    (hTyped : ∀ vals m a, Veir.interpretOp' opType properties resultTypes operands' blockOperands
      mem' = .ok (vals, m, a) → RuntimeValue.ArrayConforms vals types) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 types)
      (interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' opType properties resultTypes operands blockOperands mem regions) := by
  subst hType
  have := riscv_interpretOp'ContextuallyMonotone hLoad
  rw [interpretOp'_riscv, interpretOp'_riscv]
  exact sim_monadLift_of_isRefinedBy (Interp.isRefinedBy_and
    (this.monotone properties resultTypes operands operands' blockOperands mem mem' h hMem)
    fun ⟨vals, m, a⟩ hok => hTyped vals m a hok)

end Veir.CTree

namespace Veir

/--
Every RISC-V opcode but the loads is monotone in CTrees, with the results of the target typed: the
obligation of `OpCode.interpretCTree_monotone` holds for it. The types of the results come from
`OpCode.resultsConform_riscv`.
-/
theorem OpCode.interpretCTree_monotone_riscv (op : Riscv) (hLoad : op.isLoad = false) :
    OpCode.interpretCTree_monotone (.riscv op) := by
  intro ctx o oIn hType hVerified sv tv sm tm hConf hRef hMem
  simp only [OperationPtr.interpretCTree]
  refine CTree.riscv_sim_typed hType hLoad _ _ _ _ _ hRef hMem fun vals m a hok =>
    OpCode.resultsConform_def.mp (OpCode.resultsConform_riscv op) ctx o oIn hType hVerified
      tv vals tm m a (hConf.of_isRefinedBy hRef) ?_
  simp only [OperationPtr.interpret]
  rw [OperationPtr.getOpType!_eq_getOpType oIn, OperationPtr.getProperties!_eq_getProperties oIn
    (by grind), OperationPtr.getResultTypes!_eq_getResultTypes oIn,
    OperationPtr.getSuccessors!_eq_getSuccessors oIn]
  exact hok

/--
info: 'Veir.OpCode.interpretCTree_monotone_riscv' depends on axioms: [propext,
 Sim,
 Classical.choice,
 Quot.sound,
 Sim.ret,
 Sim.ub]
-/
#guard_msgs in
#print axioms OpCode.interpretCTree_monotone_riscv

/--
A Boolean that is `false`. Instance resolution decides it by reduction, which lets an instance
hold for the opcodes for which a reducible predicate is `false`.
-/
class Riscv.IsFalse (b : Bool) : Prop where
  eq_false : b = false

instance : Riscv.IsFalse false := ⟨rfl⟩

/-- Every RISC-V opcode but the loads meets its CTree obligation. -/
instance (op : Riscv) [h : Riscv.IsFalse op.isLoad] : InterpretCTreeMonotone (.riscv op) :=
  ⟨OpCode.interpretCTree_monotone_riscv op h.eq_false⟩

end Veir

end
