module

public import Veir.Interpreter.CTreeRefinement.ClosedCFG
public import Veir.Interpreter.Refinement.CFG
public import Veir.Interpreter.CTreeRefinement.Monotone

public section

/-!
# Simulation of closed control-flow graphs

The closed CFG loop `interpretCFGTree` takes one step per block entry and one per operation. Two
CFGs related by a transformation that inserts or fuses operations do not take their steps in
lockstep, which `CTree.Sim.iter` needs. Grouping every operation step with the step before it
(`CTree.spliceWhile`) leaves one step per block, which runs the whole block. A relation between
block calls that each grouped step re-establishes then gives a simulation of the whole loops.

`Sim` takes the target tree first: `Sim RR target source` says that every behavior of the target
is one of the source, with results related by `RR target source`.
-/

open CTree

namespace Veir.CTree

/-! ## Grouping the steps of a block -/

variable {ctx ctx' : WfIRContext OpCode}

/-- A state of the closed CFG loop. -/
abbrev CFGState (ctx : WfIRContext OpCode) : Type :=
  interpretCFG.StateLocation ctx × InterpreterState ctx

/-- What a closed CFG loop returns. -/
abbrev CFGResult (ctx : WfIRContext OpCode) : Type :=
  InterpreterState ctx × Array RuntimeValue

/-- One step of the closed CFG loop. -/
@[expose]
def cfgStep (current : CFGState ctx) : Tree (CFGState ctx ⊕ CFGResult ctx) :=
  interpretCFGTreeStep current.1 current.2

/-- Whether the loop is about to run an operation, rather than enter a block. -/
@[expose]
def CFGState.atOperation (current : CFGState ctx) : Bool :=
  current.1.isRight

/-- A step that runs a whole block: enter it, and run its operations up to its terminator. -/
@[expose]
def blockStep : CFGState ctx → Tree (CFGState ctx ⊕ CFGResult ctx) :=
  spliceWhile cfgStep CFGState.atOperation

theorem iter_cfgStep_eq_iter_blockStep (current : CFGState ctx) :
    _root_.CTree.iter cfgStep current = _root_.CTree.iter blockStep current :=
  iter_spliceWhile _ _ _

/-- The loop state of a call of a block. -/
@[expose]
def CFGState.entry {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (values : Array RuntimeValue) (state : InterpreterState ctx) : CFGState ctx :=
  (.inl (⟨block, blockIn⟩, values), state)

/-- Two loop states that are calls of blocks related by `Rel`. -/
@[expose]
def EntryRel (Rel : BlockCallRel ctx ctx') (target : CFGState ctx') (source : CFGState ctx) :
    Prop :=
  ∃ (block : BlockPtr) (blockIn : block.InBounds ctx.raw) (values : Array RuntimeValue)
    (state : InterpreterState ctx) (block' : BlockPtr) (blockIn' : block'.InBounds ctx'.raw)
    (values' : Array RuntimeValue) (state' : InterpreterState ctx'),
    source = CFGState.entry blockIn values state ∧
    target = CFGState.entry blockIn' values' state' ∧
    Rel block values state block' values' state'

/--
If the grouped steps of related block calls end in related block calls again, or return results
related by `R`, then the closed CFG loops from related block calls simulate each other.
-/
theorem iter_cfgStep_sim {Rel : BlockCallRel ctx ctx'} {R : CFGResult ctx → CFGResult ctx' → Prop}
    (hStep : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw) values state
      (block' : BlockPtr) (blockIn' : block'.InBounds ctx'.raw) values' state',
      Rel block values state block' values' state' →
      Sim (Sum.LiftRel (EntryRel Rel) (fun t s => R s t))
        (blockStep (CFGState.entry blockIn' values' state'))
        (blockStep (CFGState.entry blockIn values state)))
    {block : BlockPtr} (blockIn : block.InBounds ctx.raw) {values state}
    {block' : BlockPtr} (blockIn' : block'.InBounds ctx'.raw) {values' state'}
    (hRel : Rel block values state block' values' state') :
    Sim (fun t s => R s t)
      (_root_.CTree.iter cfgStep (CFGState.entry blockIn' values' state'))
      (_root_.CTree.iter cfgStep (CFGState.entry blockIn values state)) := by
  rw [iter_cfgStep_eq_iter_blockStep, iter_cfgStep_eq_iter_blockStep]
  refine Sim.iter (RRi := EntryRel Rel) _ _ _ _
    ⟨block, blockIn, values, state, block', blockIn', values', state', rfl, rfl, hRel⟩ ?_
  rintro _ _ ⟨block, blockIn, values, state, block', blockIn', values', state', rfl, rfl, hRel⟩
  exact hStep block blockIn values state block' blockIn' values' state' hRel

end Veir.CTree
