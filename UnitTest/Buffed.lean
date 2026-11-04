module

public import Veir.Buffered.IR.Buffed.ArgumentFlattening
public import Lean

open Veir.Buffered
open Lean Meta Compiler

public section
namespace UnitTest.Buffed

/-- The outer struct must not cross the noinline call boundary. -/
buffed (inline := false) def addressSim (p : Sim.OperationPtr) : UInt64 := p.impl

@[noinline]
def rawCaller (raw : UInt64) : UInt64 :=
  address ⟨raw, .mk { id := raw.toNat }⟩

-- `unfold` reaches the original body, not a call to addressSim/Inner.
example (p : Sim.OperationPtr) : address p = p.impl := by rw [address.unfold]
example (p : Sim.OperationPtr) : address p = addressSim p := rfl
example (p : Sim.OperationPtr) : addressInner p.impl p.spec' = p.impl := rfl

buffed def identitySim {α : Type u} (x : α) : α := x
example {α : Type u} (x : α) : identity x = x := by rw [identity.unfold]

buffed def pairSim {α : Type u} {β : Type v} (x : α) (y : β) := (y, x)
example {α : Type u} {β : Type v} (x : α) (y : β) : pair x y = (y, x) := by rw [pair.unfold]

buffed def defaultedSim (p : Sim.OperationPtr) (n : Nat := 2) : UInt64 := p.impl + n.toUInt64
example (p : Sim.OperationPtr) : defaulted p = p.impl + 2 := by rw [defaulted.unfold] <;> rfl

private def offset (x : UInt64) := x + 7
buffed (inline := false) def helperSim (p : Sim.OperationPtr) := offset p.impl
example (p : Sim.OperationPtr) : helper p = p.impl + 7 := by rw [helper.unfold]

private theorem privateProof : (0 : Nat) = 0 := rfl
buffed def certifiedSim (p : Sim.OperationPtr) : { _q : Sim.OperationPtr // (0 : Nat) = 0 } :=
  ⟨p, privateProof⟩
example (p : Sim.OperationPtr) : certified p = ⟨p, rfl⟩ := by rw [certified.unfold]

-- Nothing is done to arrays, ordinary options, or the return type.
buffed (inline := false) def containersSim
    (xs : Array Sim.OperationPtr) (x : Option Sim.OperationPtr) := (xs, x)
example (xs : Array Sim.OperationPtr) (x : Option Sim.OperationPtr) :
    containers xs x = (xs, x) := by rw [containers.unfold]

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

-- Context parameters, typeclasses, dependent proofs, erased fields,
-- and dependent result types must all survive without casts or new specifications.
buffed (inline := false) def dependentSim (ctx : Sim.IRContext OpInfo)
    (p : Sim.OperationPtr) (n : Nat) (h : p.spec.id = n)
    (_hc : ctx.spec = ctx.spec) {α : Type v} (x : α) :
    { q : Sim.OperationPtr // q.spec.id = n } × α := (⟨p, h⟩, x)

example (ctx : Sim.IRContext OpInfo) (p : Sim.OperationPtr) (n : Nat)
    (h : p.spec.id = n) (hc : ctx.spec = ctx.spec) {α : Type v} (x : α) :
    dependent ctx p n h hc x = (⟨p, h⟩, x) := by rw [dependent.unfold]

buffed (inline := false) def contextSim (ctx : Sim.IRContext OpInfo) : Sim.IRContext OpInfo := ctx
example (ctx : Sim.IRContext OpInfo) : context ctx = ctx := by rw [context.unfold]

buffed (inline := false) def contextSizeSim (ctx : Sim.IRContext OpInfo) : UInt64 :=
  ctx.buf.size.toUInt64

@[noinline]
def rawContextCaller (buf : Buffed.IRBufContext) (spec : Erased (IRContext OpInfo))
    (sim : Sim ⟨buf, spec⟩) : UInt64 := contextSize ⟨buf, spec, sim⟩

buffed (inline := false) def rawContextSim (ctx : Sim.RawIRContext OpInfo) := ctx.buf

-- Recursive inners run the rewritten body and recurse on fields. Their checked
-- equivalence and unfolding equations still describe the original function.
-- Recursive inners must be noinline even with an explicit true flag or the default.
buffed (inline := true) def countSim (p : Sim.OperationPtr) (n : Nat) : UInt64 :=
  match n with
  | 0 => p.impl
  | n + 1 => countSim p n + 1
example (p : Sim.OperationPtr) : count p 0 = p.impl := by rw [count.unfold]; rfl

buffed def strideSim (p : Sim.OperationPtr) (n : Nat) : UInt64 :=
  if h : n < 2 then p.impl else strideSim p (n - 2) + 1
termination_by n
decreasing_by omega
example (p : Sim.OperationPtr) : stride p 0 = p.impl := by rw [stride.unfold] <;> rfl

-- The pointer changes on each step; flattening only the outer entry is insufficient.
buffed (inline := false) def advanceSim (p : Sim.OperationPtr) (n : Nat) : UInt64 :=
  match n with
  | 0 => p.impl
  | n + 1 => advanceSim ⟨p.impl + 1, .mk { id := (p.impl + 1).toNat }⟩ n

buffed (inline := false) def namedRecSim {p : Sim.OperationPtr} (n : Nat)
    (step : UInt64 := 1) : UInt64 :=
  match n with
  | 0 => p.impl
  | n + 1 => @namedRecSim p n (step := step) + step

buffed (inline := false) def dependentRecSim {α : Type u} (p : Sim.OperationPtr)
    (n : Nat) (x : α) : { q : Sim.OperationPtr // q.spec = p.spec } × α :=
  match n with
  | 0 => (⟨p, rfl⟩, x)
  | n + 1 => dependentRecSim p n x

buffed (inline := false) def contextRecSim (ctx : Sim.IRContext OpInfo) (n : Nat) : UInt64 :=
  match n with
  | 0 => ctx.buf.size.toUInt64
  | n + 1 => contextRecSim ctx n + 1

-- Fixed-point equality is proved by admissible reindexing, not termination or rfl.
-- `spec'` becomes a fixed inner parameter in the first example.
buffed (inline := true) def partialWalkSim (p : Sim.OperationPtr) (n : Nat) : Option UInt64 :=
  if n = 0 then some p.impl else partialWalkSim p (n - 1)
partial_fixpoint

-- No built-in CCPO on UInt64: also exercises the compiler's inhabited flat order.
buffed def partialAdvanceSim (p : Sim.OperationPtr) (n : Nat := 0) : UInt64 :=
  if n = 0 then p.impl
  else partialAdvanceSim ⟨p.impl + 1, .mk { id := (p.impl + 1).toNat }⟩ (n - 1)
partial_fixpoint

-- Nonterminating for nonzero n: equality must not assume termination. The base case
-- also prevents Lean from compiling an argument-free cyclic global initializer.
buffed (inline := false) def partialNeverSim (p : Sim.OperationPtr) (n : Nat) : Option UInt64 :=
  if n = 0 then some p.impl else partialNeverSim p (n + 1)
partial_fixpoint

buffed def shadowSim (p : Sim.OperationPtr) (n : Nat) : UInt64 :=
  let shadowSim := fun n : Nat => p.impl + n.toUInt64
  shadowSim n

example (p : Sim.OperationPtr) (n : Nat) : advance p n = advanceSim p n := advance.eq_sim p n
example (p : Sim.OperationPtr) : partialWalk p 0 = some p.impl := by rw [partialWalk.unfold]; rfl
example (p : Sim.OperationPtr) : partialAdvance p 0 = p.impl := by rw [partialAdvance.unfold]; rfl

buffed (inline := false) def Qualified.walkSim (p : Sim.OperationPtr) (n : Nat) : UInt64 :=
  match n with
  | 0 => p.impl
  | n + 1 => walkSim p n

private buffed (inline := false) def hiddenCountSim (p : Sim.OperationPtr) (n : Nat) : UInt64 :=
  match n with
  | 0 => p.impl
  | n + 1 => hiddenCountSim p n
example (p : Sim.OperationPtr) (n : Nat) : hiddenCount p n = hiddenCountSim p n := hiddenCount.eq_sim p n

private buffed (inline := false) def hiddenSim (p : Sim.BlockPtr) := p.impl
example (p : Sim.BlockPtr) : hidden p = p.impl := by rw [hidden.unfold]

-- Match auxiliaries and nontrivial result shapes are left intact.
buffed (inline := false) def wrappedOptionSim (p : Sim.OperationPtr) (b : Bool) : Option Sim.OperationPtr :=
  if b then some p else none
example (p : Sim.OperationPtr) (b : Bool) : wrappedOption p b = if b then some p else none := by
  rw [wrappedOption.unfold]

-- Exercise the complete pointer family, including optional and generic pointers.
run_cmd do
  for type in #[``Sim.OperationPtr, ``Sim.OptionOperationPtr, ``Sim.BlockPtr,
      ``Sim.OptionBlockPtr, ``Sim.RegionPtr, ``Sim.OptionRegionPtr,
      ``Sim.OpResultPtr, ``Sim.OptionOpResultPtr, ``Sim.BlockArgumentPtr,
      ``Sim.OptionBlockArgumentPtr, ``Sim.OpOperandPtr, ``Sim.OptionOpOperandPtr,
      ``Sim.BlockOperandPtr, ``Sim.OptionBlockOperandPtr, ``Sim.ValuePtr,
      ``Sim.OptionValuePtr, ``Sim.OpOperandPtrPtr, ``Sim.BlockOperandPtrPtr,
      ``Sim.GenericPtr, ``Sim.OptionGenericPtr] do
    let name := mkIdent (.mkSimple (type.getString! ++ "RoundtripSim"))
    let type := mkIdent type
    Elab.Command.elabCommand (← `(buffed (inline := false) def $name (p : $type) : $type := p))

@[expose] buffed (inline := true) def implicitSim {p : Sim.BlockPtr} := p.impl
example (p : Sim.BlockPtr) : implicit (p := p) = p.impl := by rw [implicit.unfold]

/-- error: buffed: expected a definition with a `Sim` suffix -/
#guard_msgs in
buffed def missingSuffix (n : Nat) := n

private opaque opaqueValue : UInt64 := 0
/-- error: buffed: cannot export unfolding equation; non-exported constant UnitTest.Buffed.opaqueValue -/
#guard_msgs in
buffed def opaqueHelperSim (p : Sim.OperationPtr) := opaqueValue + p.impl

run_meta do
  let env ← getEnv
  for name in #[``addressSim, ``address, ``identitySim, ``identity, ``identityInner,
      ``implicitInner, ``shadowInner, ``countSim, ``count, ``partialWalkSim, ``partialWalk] do
    unless getInlineAttribute? env name == some .inline do
      throwError "missing inline attribute on {name}"
  for name in #[``addressInner, ``dependentInner, ``contextInner, ``countInner,
      ``strideInner, ``advanceInner, ``namedRecInner, ``dependentRecInner, ``contextRecInner,
      ``partialWalkInner, ``partialAdvanceInner, ``partialNeverInner,
      ``Qualified.walkInner, ``hiddenCountInner] do
    unless getInlineAttribute? env name == some .noinline do
      throwError "missing noinline attribute on {name}"
  for (name, arity) in #[( ``addressInner, 2), (``contextInner, 7),
      (``rawContextInner, 4), (``GenericPtrRoundtripInner, 2),
      (``OptionGenericPtrRoundtripInner, 2)] do
    forallTelescope (← getConstInfo name).type fun xs _ => do
      unless xs.size == arity do throwError "unexpected arity for {name}: {xs.size}"
  for name in #[``addressInner, ``address, ``countInner, ``count] do
    unless (← getConstInfoDefn name).all == [name] do
      throwError "generated definition has incorrect mutual-block metadata: {name}"
  forallTelescope (← getConstInfo ``address.unfold).type fun _ eq => do
    let some (_, _, rhs) := eq.eq? | throwError "expected unfolding equality"
    if rhs.getUsedConstants.contains ``addressSim || rhs.getUsedConstants.contains ``addressInner then
      throwError "unfolding stopped at a wrapper instead of the original body"
  unless (← isDefEq (← getConstInfo ``containersInner).type (← getConstInfo ``containersSim).type) do
    throwError "ordinary arrays/options were transformed"
  for name in #[``address.unfold, ``dependent.unfold, ``context.unfold, ``count.unfold,
      ``certified.unfold, ``stride.eq_sim, ``advance.unfold, ``namedRec.unfold,
      ``dependentRec.unfold, ``contextRec.unfold, ``partialWalk.unfold, ``partialAdvance.unfold,
      ``partialWalk.eq_sim, ``partialAdvance.eq_sim, ``partialNever.eq_sim,
      ``Qualified.walk.unfold, ``hiddenCount.unfold] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected axioms in {name}: {axioms}"
  for suffix in ["Impl", "Spec"] do
    if env.contains (.str `UnitTest.Buffed ("address" ++ suffix)) then
      throwError "the argument-only generator produced an unwanted {suffix} declaration"

def checkContext (ctx : Sim.IRContext OpInfo) : IO Unit := do
  unless rawContextCaller ctx.buf ctx.spec' ctx.sim == ctx.buf.size.toUInt64 do
    throw (IO.userError "flattened context call")
  unless contextRec ctx 10 == ctx.buf.size.toUInt64 + 10 do
    throw (IO.userError "flattened recursive context call")

def runTests : IO Unit := do
  for n in [:100] do
    let p : Sim.OperationPtr := ⟨n.toUInt64, .mk { id := n }⟩
    unless rawCaller n.toUInt64 == n.toUInt64 do throw (IO.userError "flattened pointer call")
    unless count p 10 == n.toUInt64 + 10 do throw (IO.userError "flattened recursive call")
    unless stride p 10 == n.toUInt64 + 5 do throw (IO.userError "flattened well-founded call")
    unless advance p 10 == n.toUInt64 + 10 do throw (IO.userError "flattened changing pointer")
    unless namedRec (p := p) 10 == n.toUInt64 + 10 do throw (IO.userError "flattened named arguments")
    unless (dependentRec p 10 n).2 == n do throw (IO.userError "flattened dependent result")
    unless partialWalk p 10 == some n.toUInt64 do throw (IO.userError "flattened option fixed point")
    unless partialAdvance p 10 == n.toUInt64 + 10 do throw (IO.userError "flattened flat-order fixed point")
    unless shadow p 10 == n.toUInt64 + 10 do throw (IO.userError "shadowed recursive name")
    unless hiddenCount p 10 == n.toUInt64 do throw (IO.userError "private recursive call")
    unless Qualified.walk p 10 == n.toUInt64 do throw (IO.userError "qualified recursive call")
    unless (wrappedOption p true).isSome && (wrappedOption p false).isNone do
      throw (IO.userError "flattened optional result")
    unless (containers #[p] (some p)).1.size == 1 do
      throw (IO.userError "ordinary pointer array")

end UnitTest.Buffed
