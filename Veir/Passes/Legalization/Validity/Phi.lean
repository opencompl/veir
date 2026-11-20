module

public import Veir.Passes.Legalization.Validity.Common
public import Veir.Passes.Legalization.LegalizerHelper
public import Veir.Interpreter.CTreeRefinement.OpList
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Interpreter.CTreeInterpreter
import all Veir.IR.Attribute

public section

namespace Veir.Legalization.CTreeProofs

open _root_.CTree

/-- Every choice made by the extension on an incoming edge produces a value that the truncation
at block entry maps back to the original argument. Both operations preserve memory and continue
without a control-flow action. -/
theorem returns_widenedBlockArgument {type : IntegerType} {width : Nat}
    (wider : type.bitwidth < width) (value : Data.LLVM.Int type.bitwidth) (mem : MemoryState) :
    Veir.CTree.Returns (Veir.CTree.interpretOp' (.gmir .g_anyext) ()
      #[(IntegerType.signless width : TypeAttr)] #[.int type.bitwidth value] #[] mem)
      (fun r => ∃ extended : Data.LLVM.Int width, r = (#[.int width extended], mem, none) ∧
        ∀ memory, Veir.CTree.interpretOp' (.gmir .g_trunc) { nsw := false, nuw := false }
          #[(type : TypeAttr)] #[.int width extended] #[] memory =
            pure (#[.int type.bitwidth value], memory, none)) := by
  have hn : ¬width ≤ type.bitwidth := Nat.not_le_of_gt wider
  change Veir.CTree.Returns (if h : width ≤ type.bitwidth then fail else
    _root_.CTree.CTree.tau (.mk (width - type.bitwidth)) (fun msb =>
      pure (#[RuntimeValue.int width (value.ext width msb (by omega))], mem, none))) _
  rw [dite_eq_right hn, _root_.CTree.CTree.tau_def]
  refine (Sim.tau_l _ _ _ _).mpr fun msb => Veir.CTree.returns_pure.mpr ?_
  refine ⟨_, rfl, fun memory => ?_⟩
  change monadLift (if h : type.bitwidth ≥ width then Interp.fail none else
    Interp.ok (#[RuntimeValue.int type.bitwidth
      ((value.ext width msb wider).trunc type.bitwidth false false (by omega))], memory, none)) = _
  rw [dite_eq_right hn, Data.LLVM.trunc_ext]
  rfl

/-- The successful type check identifies the concrete source type of each selected argument. -/
theorem widenBlockArgumentsChecked_argumentType {ctx ctx' : WfIRContext OpCode}
    {block : BlockPtr} {args : List (Nat × Nat)} {i width : Nat}
    (run : widenBlockArgumentsChecked block args ctx = .ok ctx') (selected : (i, width) ∈ args) :
    i < block.getNumArguments! ctx.raw ∧
      ∃ bits, (block.getArgument i).getType! ctx.raw = (IntegerType.signless bits : TypeAttr) ∧
        0 < bits ∧ bits < width := by
  have narrow := List.all_eq_true.mp (widenBlockArgumentsChecked_narrow run) (i, width) selected
  change LegalizerInfo.narrowerArgument block ctx.raw i width = true at narrow
  unfold LegalizerInfo.narrowerArgument at narrow
  split at narrow
  next arg hArg =>
    obtain ⟨bound, h⟩ := Array.getElem?_eq_some_iff.mp hArg
    have index : i < block.getNumArguments! ctx.raw := by simpa using bound
    have hPtr : arg = block.getArgument i := h.symm.trans
      (BlockPtr.getArguments!.getElem_eq_getArgument index)
    rw [hPtr] at narrow
    split at narrow
    next bits typeEq =>
      obtain ⟨pos, lt⟩ : 0 < bits ∧ bits < width := by simpa using narrow
      rw [ValuePtr.getType!_blockArgument] at typeEq
      refine ⟨index, bits, Subtype.ext ?_, pos, lt⟩
      simpa only [TypeAttr.of_def, ← Attribute.integerType_eq_of, IntegerType.signless] using typeEq
    all_goals contradiction
  next => contradiction

end Veir.Legalization.CTreeProofs
