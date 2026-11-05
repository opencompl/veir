module

import UnitTest.Buffed

open Veir UnitTest.Buffed

-- Generated declarations and unfolding equations remain usable across modules,
-- including equations whose source definition has match auxiliaries or recursion.
example (p : Sim.OperationPtr) : address p = p.impl := by rw [address.unfold]
example (p : Sim.OperationPtr) (b : Bool) :
    wrappedOption p b = if b then some p else none := by rw [wrappedOption.unfold]
example (p : Sim.OperationPtr) (n : Nat) :
    count p (n + 1) = countSim p n + 1 := by rw [count.unfold]
example {α : Type u} (x : α) : identity x = x := by rw [identity.unfold]
example (p : Sim.OperationPtr) : defaulted p = p.impl + 2 := by rw [defaulted.unfold] <;> rfl
example (p : Sim.OperationPtr) : helper p = p.impl + 7 := by rw [helper.unfold]
example (p : Sim.OperationPtr) : certified p = ⟨p, rfl⟩ := by rw [certified.unfold]
example (p : Sim.OperationPtr) : stride p 0 = p.impl := by rw [stride.unfold] <;> rfl
example (p : Sim.OperationPtr) (n : Nat) : advance p n = advanceSim p n := by rw [advance.eq_sim]
example (p : Sim.OperationPtr) : partialWalk p 0 = some p.impl := by rw [partialWalk.unfold]; rfl
example (p : Sim.OperationPtr) (n : Nat) : partialAdvance p n = partialAdvanceSim p n :=
  partialAdvance.eq_sim p n
example {α : Type u} (p : Sim.OperationPtr) (n : Nat) (x : α) :
    dependentRec p n x = dependentRecSim p n x := by rw [dependentRec.eq_sim]

example (p : Sim.OperationPtr) (n : Nat) :
    partialPointer p n = partialPointerSim p n := partialPointer.eq_sim p n
example (p : Sim.OperationPtr) : partialNeverPointer p 0 = some p := by
  rw [partialNeverPointer.unfold]
  simp

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
example (ctx : Sim.IRContext OpInfo) : keepContext ctx = ctx := by rw [keepContext.unfold]
example (ctx : Sim.IRContext OpInfo) (p : Sim.OperationPtr) (n : Nat)
    (h : p.spec.id = n) (hc : ctx.spec = ctx.spec) {α : Type u} (x : α) :
    dependent ctx p n h hc x = (⟨p, h⟩, x) := by rw [dependent.unfold]
