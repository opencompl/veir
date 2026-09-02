module

public import Mathlib.Data.ZMod.Basic
public import Veir.IR.Basic
public import Veir.GlobalOpInfo

/-!
# LLZK constraint semantics

Models a constraint body as a predicate over assignments to block arguments.
The modulus is explicit; supported Felt operations compute field values and
`constrain.eq` contributes equality constraints.

-/

namespace Veir.LLZK.Semantics

public section

/-! ## Expressions -/

/-- A free variable in the constraint system. -/
abbrev Signal := Nat

/-- An assignment of field elements to signals. -/
abbrev Assignment (p : Nat) := Signal → ZMod p

/-- A tree-shaped Felt expression. -/
inductive FeltExpr where
  | sig   (s : Signal)
  | const (n : Int)
  | add   (a b : FeltExpr)
  | mul   (a b : FeltExpr)
  | neg   (a : FeltExpr)
deriving Repr, DecidableEq, Inhabited

/-- Evaluate an expression under an assignment. Constants use the ring
    homomorphism `ℤ → ZMod p`. -/
@[grind]
def FeltExpr.eval {p : Nat} (σ : Assignment p) : FeltExpr → ZMod p :=
  fun e => match e with
    | .sig s => σ s
    | .const n => (n : ZMod p)
    | .add a b => a.eval σ  + b.eval σ
    | .mul a b => a.eval σ  * b.eval σ
    | .neg a => - a.eval σ

/-- Adding a zero constant changes nothing, in every modulus. -/
theorem eval_add_const_zero {p : Nat} (σ : Assignment p) (e : FeltExpr) :
    (FeltExpr.add e (FeltExpr.const 0)).eval σ = e.eval σ := by
    grind

/-- Constant addition is valid for every modulus. -/
theorem eval_const_add {p : Nat} (σ : Assignment p) (a b : Int) :
    (FeltExpr.add (FeltExpr.const a) (FeltExpr.const b)).eval σ
      = (FeltExpr.const (a + b)).eval σ := by
  simp only [FeltExpr.eval, Int.cast_add]



/-! ## IR traversal -/

/-- The field value computed for each SSA value. -/
abbrev ValEnv (p : Nat) := Std.HashMap ValuePtr (ZMod p)

/-- Collect the operations reachable from `op` by following the block's linked
    list. The decreasing measure comes from well-formedness of that list. -/

def op_chain (ctx : WfIRContext OpCode) (op: OperationPtr) (hop : op.InBounds ctx.raw := by grind) : List OperationPtr :=
  match h: (op.get ctx.raw).next with
  | none => [op]
  | some next => op :: op_chain ctx next
termination_by op.idxInParentFromTail ctx.raw
decreasing_by grind

def opsOf (ctx : WfIRContext OpCode) (blk : BlockPtr) (hblk: blk.InBounds ctx.raw := by grind) : List OperationPtr :=
  match h : (blk.get! ctx.raw).firstOp with
  | none => []
  | some op => op_chain ctx op

/-- Evaluate one field-native felt operation from its operand values. Returns
    `none` for operations outside the modelled const/add/sub/mul/neg fragment. -/
def evalFeltOp {p : Nat} (ctx : IRContext OpCode) (op : OperationPtr)
    (env : ValEnv p) : Option (ZMod p) :=
  match op.getOpType! ctx with
  | .felt .const => some (op.getProperties! ctx (OpCode.felt Felt.const)).value.value
  | .felt .add => do return (← env[op.getOperand! ctx 0]?) + (← env[op.getOperand! ctx 1]?)
  | .felt .sub => do return (← env[op.getOperand! ctx 0]?) - (← env[op.getOperand! ctx 1]?)
  | .felt .mul => do return (← env[op.getOperand! ctx 0]?) * (← env[op.getOperand! ctx 1]?)
  | .felt .neg => do return -(← env[op.getOperand! ctx 0]?)
  | _ => none


/-- Seed the environment from the block's felt arguments:
    argument `i` gets the value `σ i`. -/
def seedBlockArgs {p : Nat} (ctx : IRContext OpCode) (blk : BlockPtr)
  (σ : Assignment p) : ValEnv p := Id.run do
  let args := blk.getArguments! ctx
  let mut valenv := Std.HashMap.emptyWithCapacity
  for h: i in [0:args.size] do
    let argi := args[i]
    let argiType := (argi.getType! ctx).val
    match argiType with
    | .feltType _ => valenv := valenv.insert argi (σ i)
    | _ => continue

  valenv


/-- Evaluate supported Felt operations and collect `constrain.eq` operand pairs.

Returns `none` for operations outside the supported fragment.
-/
@[expose]
def evalBody {p : Nat} (ctx : IRContext OpCode) (ops : List OperationPtr)
    (env₀ : ValEnv p) : Option (ValEnv p × List (ZMod p × ZMod p)) :=
  match ops with
  | [] => some (env₀, [])
  | op :: ops =>
    match op.getOpType! ctx with
    | .constrain .eq => do
      let lhs ← env₀[op.getOperand! ctx 0]?
      let rhs ← env₀[op.getOperand! ctx 1]?
      let (env, cs) ← evalBody ctx ops env₀
      return (env, (lhs, rhs) :: cs)
    | _ => do
      let v ← evalFeltOp ctx op env₀
      evalBody ctx ops (env₀.insert (op.getResult 0) v)

/-! ## Satisfaction -/

/-- The proposition that every constraint in `blk` holds under `σ`. -/
@[grind]
def IRSat {p : Nat} (ctx : WfIRContext OpCode) (blk : BlockPtr) (hBlock: blk.InBounds ctx.raw := by grind)
    (σ : Assignment p) : Prop :=
  match evalBody ctx (blk.operationList ctx.raw).toList (seedBlockArgs ctx blk σ) with
  | none => False
  | some (e, c) => ∀ (lhs rhs: ZMod p), (lhs, rhs) ∈ c → lhs = rhs

/-- Executable satisfaction check using the linked-list traversal `opsOf`. -/
def irsatb {p : Nat} (ctx : WfIRContext OpCode) (blk : BlockPtr) (hblk: blk.InBounds ctx.raw)
    (σ : Assignment p) : _root_.Bool :=
  let r := evalBody ctx (opsOf ctx blk) (seedBlockArgs ctx blk σ)
  match r with
  | none => false
  | some (_, v) => v.all (fun (x, y) => x = y)

theorem op_chain_eq_drop (ctx : WfIRContext OpCode) (blk : BlockPtr)
    {array : _root_.Array OperationPtr} (hchain : BlockPtr.OpChain blk ctx.raw array) (n : Nat) :
    ∀ (i : Nat) (_hin : i + n = array.size) (hi : i < array.size)
      (hop : array[i].InBounds ctx.raw),
      op_chain ctx array[i] hop = array.toList.drop i := by
  induction n with
  | zero => grind
  | succ n ih =>
    intro i hin hi hop
    have hnext := hchain.next hi
    rw [op_chain]
    split
    · grind [List.drop_eq_getElem_cons]
    · grind [List.drop_eq_getElem_cons]


theorem opsOf_eq_operationList (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (hBlock : blk.InBounds ctx.raw) :
    opsOf ctx blk hBlock = (blk.operationList ctx.raw).toList := by
  have hchain := BlockPtr.operationListWF ctx.raw blk hBlock ctx.wellFormed
  have hfirst := hchain.first
  have hdrop := op_chain_eq_drop ctx blk hchain (blk.operationList ctx.raw).size 0
  unfold opsOf
  split
  · grind [_root_.Array.toList_eq_nil_iff, _root_.Array.size_eq_zero_iff]
  · grind

/-- The executable and proposition-valued satisfaction checks agree. -/
theorem irsatb_iff_IRSat {p : Nat} (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (hBlock : blk.InBounds ctx.raw) (σ : Assignment p) :
    irsatb ctx blk hBlock σ = true ↔ IRSat ctx blk hBlock σ := by
  unfold irsatb IRSat
  rw [opsOf_eq_operationList]
  split <;> simp_all


end

end Veir.LLZK.Semantics
