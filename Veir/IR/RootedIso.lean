module

public import Veir.IR.WellFormed
public import Veir.GlobalOpInfo

public section

namespace Veir

/-! Rooted isomorphism: two graphs agree on everything reachable from their roots, up to a
renaming of pointers. Unreachable operations, allocation order and use-lists are ignored. -/

/-- `op` is `root`, or lies in a block of a region of a reachable operation. -/
inductive Reaches (ctx : WfIRContext OpCode) (root : OperationPtr) : OperationPtr → Prop
  | root : Reaches ctx root root
  | nested {op r bs b os o} : Reaches ctx root op → r ∈ op.getRegions! ctx.raw →
      r.BlockChain ctx.raw bs → b ∈ bs → b.OpChain ctx.raw os → o ∈ os → Reaches ctx root o

/-- Lift a renaming of operations and blocks to values: results and arguments keep their index. -/
@[expose]
def renameValue (φ : OperationPtr → OperationPtr) (β : BlockPtr → BlockPtr) : ValuePtr → ValuePtr
  | .opResult r => .opResult { r with op := φ r.op }
  | .blockArgument a => .blockArgument { a with block := β a.block }

/-- A partial function is injective on the pointers it maps. -/
def PartialInjective (f : α → Option β) : Prop :=
  ∀ ⦃a a' b⦄, f a = some b → f a' = some b → a = a'

/-- Rename a value when its defining operation or block is mapped. -/
@[expose]
def renameValue? (φ : OperationPtr → Option OperationPtr) (β : BlockPtr → Option BlockPtr) :
    ValuePtr → Option ValuePtr
  | .opResult r => (fun o => .opResult { r with op := o }) <$> φ r.op
  | .blockArgument a => (fun b => .blockArgument { a with block := b }) <$> β a.block

/-- Observable operation fields agree, excluding the root's surrounding context and use-lists. -/
def OperationAgrees (ctx₁ ctx₂ : WfIRContext OpCode) (root : OperationPtr)
    (φ : OperationPtr → Option OperationPtr) (ρ : RegionPtr → Option RegionPtr)
    (β : BlockPtr → Option BlockPtr) (o o' : OperationPtr) : Prop :=
  o.InBounds ctx₁.raw ∧ o'.InBounds ctx₂.raw ∧
  (∀ code : OpCode, o.getProperties! ctx₁.raw code = o'.getProperties! ctx₂.raw code) ∧
  (o.getOpType! ctx₁.raw, o.getResultTypes! ctx₁.raw, o.getAttributes! ctx₁.raw) =
    (o'.getOpType! ctx₂.raw, o'.getResultTypes! ctx₂.raw, o'.getAttributes! ctx₂.raw) ∧
  (o.getOperands! ctx₁.raw).mapM (renameValue? φ β) = some (o'.getOperands! ctx₂.raw) ∧
  (o.getSuccessors! ctx₁.raw).mapM β = some (o'.getSuccessors! ctx₂.raw) ∧
  (o.getRegions! ctx₁.raw).mapM ρ = some (o'.getRegions! ctx₂.raw) ∧
  (o ≠ root → (o.getParent! ctx₁.raw).mapM β = some (o'.getParent! ctx₂.raw))

/-- Region ownership and its ordered block chain agree. -/
def RegionAgrees (ctx₁ ctx₂ : WfIRContext OpCode)
    (φ : OperationPtr → Option OperationPtr) (β : BlockPtr → Option BlockPtr)
    (r r' : RegionPtr) : Prop :=
  r.InBounds ctx₁.raw ∧ r'.InBounds ctx₂.raw ∧
  (r.getParent! ctx₁.raw).mapM φ = some (r'.getParent! ctx₂.raw) ∧
  ∀ bs, r.BlockChain ctx₁.raw bs →
    ∃ bs', bs.mapM β = some bs' ∧ r'.BlockChain ctx₂.raw bs'

/-- Block argument types, ownership, and its ordered operation chain agree. -/
def BlockAgrees (ctx₁ ctx₂ : WfIRContext OpCode)
    (φ : OperationPtr → Option OperationPtr) (ρ : RegionPtr → Option RegionPtr)
    (b b' : BlockPtr) : Prop :=
  b.InBounds ctx₁.raw ∧ b'.InBounds ctx₂.raw ∧
  b.getArgumentTypes! ctx₁.raw = b'.getArgumentTypes! ctx₂.raw ∧
  (b.getParent! ctx₁.raw).mapM ρ = some (b'.getParent! ctx₂.raw) ∧
  ∀ os, b.OpChain ctx₁.raw os →
    ∃ os', os.mapM φ = some os' ∧ b'.OpChain ctx₂.raw os'

/-- Partial bijections preserve every mapped node and reference. The root's parent and sibling
links are outside the comparison; unrelated allocations and use-lists are ignored. -/
@[expose]
def RootedIso (ctx₁ : WfIRContext OpCode) (root₁ : OperationPtr)
    (ctx₂ : WfIRContext OpCode) (root₂ : OperationPtr) : Prop :=
  ∃ (φ : OperationPtr → Option OperationPtr) (ρ : RegionPtr → Option RegionPtr)
    (β : BlockPtr → Option BlockPtr),
    PartialInjective φ ∧ PartialInjective ρ ∧ PartialInjective β ∧ φ root₁ = some root₂ ∧
    (∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root₁ φ ρ β o o') ∧
    (∀ r r', ρ r = some r' → RegionAgrees ctx₁ ctx₂ φ β r r') ∧
    (∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b')

/-- Blocks structurally contained in the rooted graph. -/
@[expose]
def ReachesBlock (ctx : WfIRContext OpCode) (root : OperationPtr) (b : BlockPtr) : Prop :=
  ∃ o, Reaches ctx root o ∧ ∃ r ∈ o.getRegions! ctx.raw,
    ∃ bs, r.BlockChain ctx.raw bs ∧ b ∈ bs

/-- All operands and successors refer to definitions inside the rooted graph. -/
@[expose]
def RootedClosed (ctx : WfIRContext OpCode) (root : OperationPtr) : Prop :=
  root.InBounds ctx.raw ∧ ∀ o, Reaches ctx root o →
    (∀ v ∈ o.getOperands! ctx.raw, match v with
      | .opResult r => Reaches ctx root r.op
      | .blockArgument a => ReachesBlock ctx root a.block) ∧
    ∀ b ∈ o.getSuccessors! ctx.raw, ReachesBlock ctx root b


section Inverse

noncomputable def inversePartial (f : α → Option β) (b : β) : Option α :=
  letI := Classical.propDecidable (∃ a, f a = some b)
  if h : ∃ a, f a = some b then some h.choose else none

theorem inversePartial_iff {f : α → Option β} (hf : PartialInjective f) :
    inversePartial f b = some a ↔ f a = some b := by
  classical
  unfold inversePartial; split
  · rename_i h; constructor
    · intro he; obtain rfl := Option.some.inj he; exact h.choose_spec
    · intro he; exact congrArg some (hf h.choose_spec he)
  · simp_all

theorem inversePartial_injective {f : α → Option β} (hf : PartialInjective f) :
    PartialInjective (inversePartial f) := by
  intro b b' a h h'
  exact Option.some.inj (((inversePartial_iff hf).mp h).symm.trans ((inversePartial_iff hf).mp h'))

theorem list_mapM_inverse {f : α → Option β} {g : β → Option α} {xs : List α} {ys : List β}
    (hf : ∀ a b, f a = some b → g b = some a) (h : xs.mapM f = some ys) :
    ys.mapM g = some xs := by
  induction xs generalizing ys with
  | nil => obtain rfl : ys = [] := (by simpa using h.symm); rfl
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hs : xs.mapM f with
      | none => simp [ha, hs] at h
      | some bs => obtain rfl : ys = b :: bs := (by simpa [ha, hs] using h.symm); simp [hf _ _ ha, ih hs]

theorem array_mapM_inverse {f : α → Option β} {g : β → Option α} {xs : Array α} {ys : Array β}
    (hf : ∀ a b, f a = some b → g b = some a) (h : xs.mapM f = some ys) :
    ys.mapM g = some xs := by
  apply Array.map_toList_inj.mp
  simpa [Array.toList_mapM] using
    list_mapM_inverse hf (show xs.toList.mapM f = some ys.toList by simp [← Array.toList_mapM, h])

theorem option_mapM_inverse {f : α → Option β} {g : β → Option α} {x : Option α} {y : Option β}
    (hf : ∀ a b, f a = some b → g b = some a) (h : x.mapM f = some y) :
    y.mapM g = some x := by
  cases x with
  | none => obtain rfl : y = none := (by simpa using h.symm); rfl
  | some a =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b => obtain rfl : y = some b := (by simpa [ha] using h.symm); simp [hf _ _ ha]

theorem renameValue_inverse {φ : OperationPtr → Option OperationPtr} {β : BlockPtr → Option BlockPtr}
    {ψ : OperationPtr → Option OperationPtr} {δ : BlockPtr → Option BlockPtr}
    (hφ : ∀ a b, φ a = some b → ψ b = some a) (hβ : ∀ a b, β a = some b → δ b = some a)
    (h : renameValue? φ β v = some v') : renameValue? ψ δ v' = some v := by
  cases v with
  | opResult r =>
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [renameValue?, hφ _ _ ho]
  | blockArgument a =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [renameValue?, hβ _ _ hb]

variable {ctx₁ ctx₂ : WfIRContext OpCode} {root₁ root₂ : OperationPtr}
variable {φ : OperationPtr → Option OperationPtr} {ρ : RegionPtr → Option RegionPtr} {β : BlockPtr → Option BlockPtr}

theorem OperationAgrees.inverse (hφ : PartialInjective φ) (hρ : PartialInjective ρ) (hβ : PartialInjective β)
    (hr : φ root₁ = some root₂) (hm : φ o = some o') (h : OperationAgrees ctx₁ ctx₂ root₁ φ ρ β o o') :
    OperationAgrees ctx₂ ctx₁ root₂ (inversePartial φ) (inversePartial ρ) (inversePartial β) o' o := by
  rcases h with ⟨hi, hi', hprops, hlabels, hvs, hss, hrs, hp⟩
  refine ⟨hi', hi, fun c => (hprops c).symm, hlabels.symm,
    array_mapM_inverse (fun _ _ => renameValue_inverse (fun _ _ => (inversePartial_iff hφ).mpr) (fun _ _ => (inversePartial_iff hβ).mpr)) hvs,
    array_mapM_inverse (fun _ _ => (inversePartial_iff hβ).mpr) hss,
    array_mapM_inverse (fun _ _ => (inversePartial_iff hρ).mpr) hrs, ?_⟩
  intro hne; apply option_mapM_inverse (fun _ _ => (inversePartial_iff hβ).mpr) (hp ?_)
  intro he; subst o; exact hne (Option.some.inj (hm.symm.trans hr))

theorem RegionAgrees.inverse (hφ : PartialInjective φ) (hβ : PartialInjective β)
    (h : RegionAgrees ctx₁ ctx₂ φ β r r') :
    RegionAgrees ctx₂ ctx₁ (inversePartial φ) (inversePartial β) r' r := by
  rcases h with ⟨hi, hi', hp, hb⟩
  refine ⟨hi', hi, option_mapM_inverse (fun _ _ => (inversePartial_iff hφ).mpr) hp, ?_⟩
  intro bs' hbs'; obtain ⟨bs, hbs⟩ := ctx₁.wellFormed.blockChain r hi
  obtain ⟨mapped, hm, hchain⟩ := hb bs hbs
  obtain rfl := RegionPtr.BlockChain_unique hbs' hchain
  exact ⟨bs, array_mapM_inverse (fun _ _ => (inversePartial_iff hβ).mpr) hm, hbs⟩

theorem BlockAgrees.inverse (hφ : PartialInjective φ) (hρ : PartialInjective ρ)
    (h : BlockAgrees ctx₁ ctx₂ φ ρ b b') :
    BlockAgrees ctx₂ ctx₁ (inversePartial φ) (inversePartial ρ) b' b := by
  rcases h with ⟨hi, hi', ha, hp, ho⟩
  refine ⟨hi', hi, ha.symm, option_mapM_inverse (fun _ _ => (inversePartial_iff hρ).mpr) hp, ?_⟩
  intro os' hos'; obtain ⟨os, hos⟩ := ctx₁.wellFormed.opChain b hi
  obtain ⟨mapped, hm, hchain⟩ := ho os hos
  obtain rfl := BlockPtr.OpChain_unique hos' hchain
  exact ⟨os, array_mapM_inverse (fun _ _ => (inversePartial_iff hφ).mpr) hm, hos⟩

theorem RootedIso.symm (h : RootedIso ctx₁ root₁ ctx₂ root₂) : RootedIso ctx₂ root₂ ctx₁ root₁ := by
  obtain ⟨φ, ρ, β, hφ, hρ, hβ, hr, ho, hreg, hblock⟩ := h
  exact ⟨inversePartial φ, inversePartial ρ, inversePartial β,
    inversePartial_injective hφ, inversePartial_injective hρ, inversePartial_injective hβ,
    (inversePartial_iff hφ).mpr hr,
    fun _ _ hm => (ho _ _ ((inversePartial_iff hφ).mp hm)).inverse hφ hρ hβ hr ((inversePartial_iff hφ).mp hm),
    fun _ _ hm => (hreg _ _ ((inversePartial_iff hρ).mp hm)).inverse hφ hβ,
    fun _ _ hm => (hblock _ _ ((inversePartial_iff hβ).mp hm)).inverse hφ hρ⟩


end Inverse

namespace RootedIso

/-- The finite graphs of the three partial bijections. -/
structure Constraints where
  operations : List (OperationPtr × OperationPtr) := []
  regions : List (RegionPtr × RegionPtr) := []
  blocks : List (BlockPtr × BlockPtr) := []

/-- A pair of nodes whose fields still need comparing. -/
inductive NodePair where
  | op : OperationPtr → OperationPtr → NodePair
  | region : RegionPtr → RegionPtr → NodePair
  | block : BlockPtr → BlockPtr → NodePair

/-- Pair ordered fields without silently discarding a longer suffix. -/
def zipExact (xs : List α) (ys : List β) : Option (List (α × β)) :=
  if xs.length = ys.length then some (xs.zip ys) else none

/-- Distinguish an absent link from a link present in only one graph. -/
def pairOptions : Option α → Option β → Option (List (α × β))
  | none, none => some []
  | some a, some b => some [(a, b)]
  | _, _ => none

/-- An operand enqueues its defining node and preserves its result or argument index. -/
def constrainValue : ValuePtr × ValuePtr → Option NodePair
  | (.opResult a, .opResult b) =>
      if a.index = b.index then some (.op a.op b.op) else none
  | (.blockArgument a, .blockArgument b) =>
      if a.index = b.index then some (.block a.block b.block) else none
  | _ => none

/-- Compare opcode-dependent properties without enumerating all opcodes. -/
def kind (ctx : WfIRContext OpCode) (o : OperationPtr) : OpKind OpCode :=
  ⟨o.getOpType! ctx.raw, o.getProperties! ctx.raw (o.getOpType! ctx.raw)⟩

/-- The root's surrounding context is excluded; all other parent and sibling links are followed. -/
def operationLinks (ctx₁ ctx₂ : WfIRContext OpCode) (root o o' : OperationPtr) :
    Option (List NodePair) :=
  if o = root then some [] else do
    let parents ← pairOptions (o.getParent! ctx₁.raw) (o'.getParent! ctx₂.raw)
    let prev ← pairOptions (o.getPrevOp! ctx₁.raw) (o'.getPrevOp! ctx₂.raw)
    let next ← pairOptions (o.getNextOp! ctx₁.raw) (o'.getNextOp! ctx₂.raw)
    return parents.map (fun (a, b) => .block a b) ++
      (prev ++ next).map (fun (a, b) => .op a b)

/-- Compare an operation's labels and collect every outgoing reference. -/
def constrainOperation (ctx₁ ctx₂ : WfIRContext OpCode) (root o o' : OperationPtr) :
    Option (List NodePair) := do
  guard (o.InBounds ctx₁.raw ∧ o'.InBounds ctx₂.raw)
  guard (kind ctx₁ o = kind ctx₂ o')
  guard (o.getResultTypes! ctx₁.raw = o'.getResultTypes! ctx₂.raw)
  guard (o.getAttributes! ctx₁.raw = o'.getAttributes! ctx₂.raw)
  let operands ← zipExact (o.getOperands! ctx₁.raw).toList (o'.getOperands! ctx₂.raw).toList
  let values ← operands.mapM constrainValue
  let successors ← zipExact (o.getSuccessors! ctx₁.raw).toList (o'.getSuccessors! ctx₂.raw).toList
  let regions ← zipExact (o.getRegions! ctx₁.raw).toList (o'.getRegions! ctx₂.raw).toList
  return values ++ successors.map (fun (a, b) => .block a b) ++
    regions.map (fun (a, b) => .region a b) ++ (← operationLinks ctx₁ ctx₂ root o o')

/-- Compare a region's parent and block-chain endpoints. -/
def constrainRegion (ctx₁ ctx₂ : WfIRContext OpCode) (r r' : RegionPtr) :
    Option (List NodePair) := do
  guard (r.InBounds ctx₁.raw ∧ r'.InBounds ctx₂.raw)
  let parents ← pairOptions (r.getParent! ctx₁.raw) (r'.getParent! ctx₂.raw)
  let first ← pairOptions (r.getFirstBlock! ctx₁.raw) (r'.getFirstBlock! ctx₂.raw)
  let last ← pairOptions (r.getLastBlock! ctx₁.raw) (r'.getLastBlock! ctx₂.raw)
  return parents.map (fun (a, b) => .op a b) ++ (first ++ last).map (fun (a, b) => .block a b)

/-- Compare a block's types, parent, sibling links, and operation-chain endpoints. -/
def constrainBlock (ctx₁ ctx₂ : WfIRContext OpCode) (b b' : BlockPtr) :
    Option (List NodePair) := do
  guard (b.InBounds ctx₁.raw ∧ b'.InBounds ctx₂.raw)
  guard (b.getArgumentTypes! ctx₁.raw = b'.getArgumentTypes! ctx₂.raw)
  let parents ← pairOptions (b.getParent! ctx₁.raw) (b'.getParent! ctx₂.raw)
  let prev ← pairOptions (b.getPrevBlock! ctx₁.raw) (b'.getPrevBlock! ctx₂.raw)
  let next ← pairOptions (b.getNextBlock! ctx₁.raw) (b'.getNextBlock! ctx₂.raw)
  let first ← pairOptions (b.getFirstOp! ctx₁.raw) (b'.getFirstOp! ctx₂.raw)
  let last ← pairOptions (b.getLastOp! ctx₁.raw) (b'.getLastOp! ctx₂.raw)
  return parents.map (fun (a, b) => .region a b) ++ (prev ++ next).map (fun (a, b) => .block a b) ++
    (first ++ last).map (fun (a, b) => .op a b)

/-- Visit each mapped node once, following references as well as containment and parent links. -/
def visit (ctx₁ ctx₂ : WfIRContext OpCode) (root : OperationPtr) :
    Nat → Constraints → NodePair → Option Constraints
  | fuel, s, pair =>
    let known := match pair with
      | .op a b => (· == b) <$> s.operations.lookup a
      | .region a b => (· == b) <$> s.regions.lookup a
      | .block a b => (· == b) <$> s.blocks.lookup a
    match known with
    | some true => some s
    | some false => none
    | none => match fuel with
      | 0 => none
      | n + 1 => do
        let pending : Option (Constraints × List NodePair) := match pair with
          | .op a b => do return ({ s with operations := (a, b) :: s.operations }, ← constrainOperation ctx₁ ctx₂ root a b)
          | .region a b => do return ({ s with regions := (a, b) :: s.regions }, ← constrainRegion ctx₁ ctx₂ a b)
          | .block a b => do return ({ s with blocks := (a, b) :: s.blocks }, ← constrainBlock ctx₁ ctx₂ a b)
        let (s, children) ← pending
        children.foldlM (visit ctx₁ ctx₂ root n) s

/-- A finite table describes a partial bijection when neither projection has conflicting entries. -/
def consistent [DecidableEq α] [DecidableEq β] (pairs : List (α × β)) : Bool :=
  pairs.all fun (a, b) => pairs.all fun (a', b') => a != a' || b == b'

def bijective [DecidableEq α] [DecidableEq β] (pairs : List (α × β)) : Bool :=
  consistent pairs && consistent (pairs.map Prod.swap)

end RootedIso

/-- Compare graphs using partial bijections, following every reference and ignoring unrelated
allocations, use-lists, and the roots' surrounding context. -/
def rootedIso? (ctx₁ : WfIRContext OpCode) (root₁ : OperationPtr)
    (ctx₂ : WfIRContext OpCode) (root₂ : OperationPtr) : Bool :=
  let fuel := ctx₁.raw.operations.size + ctx₁.raw.regions.size + ctx₁.raw.blocks.size + 1
  match RootedIso.visit ctx₁ ctx₂ root₁ fuel {} (.op root₁ root₂) with
  | none => false
  | some s => RootedIso.bijective s.operations && RootedIso.bijective s.regions && RootedIso.bijective s.blocks

/-- Correctness of the executable comparison against the declarative specification. -/
theorem rootedIso?_eq_true_iff (ctx₁ : WfIRContext OpCode) (root₁ : OperationPtr)
    (ctx₂ : WfIRContext OpCode) (root₂ : OperationPtr) :
    rootedIso? ctx₁ root₁ ctx₂ root₂ = true ↔ RootedIso ctx₁ root₁ ctx₂ root₂ := sorry

instance (ctx₁ : WfIRContext OpCode) (root₁ : OperationPtr) (ctx₂ : WfIRContext OpCode) :
    DecidablePred (RootedIso ctx₁ root₁ ctx₂) := fun root₂ =>
  decidable_of_iff (rootedIso? ctx₁ root₁ ctx₂ root₂ = true)
    (rootedIso?_eq_true_iff ctx₁ root₁ ctx₂ root₂)

end Veir
