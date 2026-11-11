module

public import Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTree
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.RISCV.Interpreter

public section

namespace Veir

open _root_.CTree

@[simp]
theorem CTree.checkResultTypes_ok_iff {types} {tree : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)} {result} :
    PureOrErr.CanInterpretTo (CTree.checkResultTypes types tree) (.ok result) ↔
      PureOrErr.CanInterpretTo tree (.ok result) ∧ RuntimeValue.ArrayConforms result.1 types := by
  simp only [CTree.checkResultTypes, Bind.bind, PureOrErr.CanInterpretTo.bind_iff]
  simp only [reduceCtorEq, and_false, or_false]
  constructor
  · rintro ⟨value, outcome, checked⟩
    split at checked
    · simp only [PureOrErr.CanInterpretTo.pure_iff, Interp.ok.injEq] at checked
      subst value
      exact ⟨outcome, ‹_›⟩
    · simp [Veir.ub, _root_.CTree.CTree.trigger_def] at checked
  · rintro ⟨outcome, conforms⟩
    exact ⟨result, outcome, by simp [conforms]⟩

/-- Result checking only introduces a return or UB. -/
theorem CTree.checkResultTypes_pureOrErr {types} {tree : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)}
    (h : PureOrErr tree) : PureOrErr (CTree.checkResultTypes types tree) := by
  apply PureOrErr.bind _ _ h
  intro result
  split
  · exact .ret _
  · simpa [Veir.ub, _root_.CTree.CTree.trigger_def, Bind.bind] using
      (PureOrErr.ub (E := ErrorE ⊕ₑ UBE) (C := FreezeC) (k := _))

/-- Lifting a deterministic interpreter outcome introduces no infinite or external behavior. -/
theorem PureOrErr.liftedInterp {EIn CIn : Type} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E] (outcome : Interp α) :
    PureOrErr (liftM outcome : CTree E C α) := by
  cases outcome <;>
    simp [liftM, monadLift, MonadLift.monadLift, Veir.fail, Veir.ub,
      _root_.CTree.CTree.trigger_def, Bind.bind]
  exact .ret _

/-- The LLVM opcode interpreter only returns, chooses, or reports failure/UB. -/
theorem Llvm.interpretOpCTree_pureOrErr (code : Llvm) (properties : propertiesOf code)
    (types : Array TypeAttr) (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (memory : MemoryState) :
    PureOrErr (Llvm.interpretOpCTree (E := ErrorE ⊕ₑ UBE)
      code properties types operands successors memory) := by
  unfold interpretOpCTree
  split
  · split
    · split
      all_goals
        repeat first
        | exact PureOrErr.ret _
        | exact PureOrErr.fail
        | split
        | simp only [CTree.choose_def, CTree.tau_def, Bind.bind, _root_.CTree.CTree.bind_tau,
            _root_.CTree.CTree.bind_ret, Pure.pure, Veir.fail, CTree.trigger_def, _root_.CTree.CTree.bind_vis]
        | apply PureOrErr.tau; intro
    · simpa only [Veir.fail, CTree.trigger_def, Bind.bind, _root_.CTree.CTree.bind_vis] using
        (PureOrErr.fail (E := ErrorE ⊕ₑ UBE) (C := FreezeC) (k := _))
  · exact PureOrErr.liftedInterp _

/-- The GMIR opcode interpreter has the same finite return/choice/error shape. -/
theorem GMIR.interpretOpCTree_pureOrErr (code : GMIR) (properties : propertiesOf code)
    (types : Array TypeAttr) (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (memory : MemoryState) :
    PureOrErr (GMIR.interpretOpCTree (E := ErrorE ⊕ₑ UBE)
      code properties types operands successors memory) := by
  unfold interpretOpCTree
  split
  · repeat first
    | exact PureOrErr.ret _
    | exact PureOrErr.fail
    | split
    | simp only [CTree.tau_def, Veir.fail, CTree.trigger_def, Bind.bind,
        _root_.CTree.CTree.bind_vis]
    | apply PureOrErr.tau; intro
  · apply PureOrErr.bind _ _ (PureOrErr.liftedInterp _)
    rintro ⟨results, mem, action⟩
    dsimp
    split
    · split
      · simp only [CTree.tau_def]
        apply PureOrErr.tau
        intro msb
        exact .ret _
      · exact .ret _
    · exact .ret _
  · exact PureOrErr.liftedInterp _

/-- Builtin conversion choices also terminate at a return, failure, or UB node. -/
theorem Builtin.interpretOpCTree_pureOrErr (code : Builtin) (properties : propertiesOf code)
    (types : Array TypeAttr) (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (memory : MemoryState) :
    PureOrErr (Builtin.interpretOpCTree (E := ErrorE ⊕ₑ UBE)
      code properties types operands successors memory) := by
  unfold interpretOpCTree
  all_goals simp only [Builtin.interpretUnrealizedConversionCastCTree]
  repeat first
  | exact PureOrErr.ret _
  | exact PureOrErr.fail (E := ErrorE ⊕ₑ UBE) (C := FreezeC)
  | split
  | simp only [Builtin.byteToIntCTree, CTree.choose_def, CTree.tau_def, Bind.bind,
      _root_.CTree.CTree.bind_tau, _root_.CTree.CTree.bind_ret,
      Pure.pure, Veir.fail, CTree.trigger_def, _root_.CTree.CTree.bind_vis]
  | apply PureOrErr.tau; intro

/-- A RISC-V load lifts a finite memory outcome and then chooses its poison bits. -/
theorem riscvLoadCTree_pureOrErr (imm12 : BitVec 12) (operands : Array RuntimeValue)
    (memory : MemoryState) (bytes : Nat) (extension : LoadExtension) :
    PureOrErr (riscvLoadCTree (E := ErrorE ⊕ₑ UBE) imm12 operands memory bytes extension) := by
  unfold riscvLoadCTree
  split
  · apply PureOrErr.bind _ _ (PureOrErr.liftedInterp _)
    intro value
    simp only [CTree.choose_def, CTree.tau_def, Bind.bind,
      _root_.CTree.CTree.bind_tau, _root_.CTree.CTree.bind_ret]
    apply PureOrErr.tau
    intro bits
    exact .ret _
  · simpa only [Veir.fail, CTree.trigger_def, Bind.bind, _root_.CTree.CTree.bind_vis] using
      (PureOrErr.fail (E := ErrorE ⊕ₑ UBE) (C := FreezeC) (k := _))

/-- RISC-V opcode execution only lifts a finite outcome or executes a finite load choice. -/
theorem Riscv.interpretOpCTree_pureOrErr (code : Riscv) (properties : propertiesOf code)
    (types : Array TypeAttr) (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (memory : MemoryState) :
    PureOrErr (Riscv.interpretOpCTree (E := ErrorE ⊕ₑ UBE)
      code properties types operands successors memory) := by
  unfold interpretOpCTree
  split <;> first
    | exact riscvLoadCTree_pureOrErr _ _ _ _ _
    | exact PureOrErr.liftedInterp _

/-- Raw opcode execution has no visible effects other than failure and UB.
This is a statement about the tree shape, not independence from the input memory. -/
theorem CTree.interpretOp'_pureOrErr (code : OpCode) (properties : propertiesOf code)
    (types : Array TypeAttr) (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (memory : MemoryState) (regions : Array RegionPtr := #[]) :
    PureOrErr (CTree.interpretOp' code properties types operands successors memory regions) := by
  cases code <;> simp only [CTree.interpretOp']
  all_goals first
    | exact Llvm.interpretOpCTree_pureOrErr _ _ _ _ _ _
    | exact GMIR.interpretOpCTree_pureOrErr _ _ _ _ _ _
    | exact CTree.checkResultTypes_pureOrErr (Builtin.interpretOpCTree_pureOrErr _ _ _ _ _ _)
    | exact CTree.checkResultTypes_pureOrErr (Riscv.interpretOpCTree_pureOrErr _ _ _ _ _ _)
    | exact PureOrErr.liftedInterp _

end Veir
