import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.Felt.Matching
namespace Veir.FeltPass

/-!
Felt-dialect peephole combines for `add`, `sub`, `mul`, and `neg`.

Simple graph projections are expressed as Puddle patterns. Rewrites that synthesize a zero
constant use the local-rewrite interface. Ordinary constant folding and commutative operand
ordering are handled by the generic `canonicalize` pass.
-/

/-! # Rewrite patterns -/

namespace PuddlePatterns

private def constant (type : Puddle.Handle OpCode .type) (value : Int) := do
  Puddle.MatchProg.operation (.felt .const) #[] #[type]
    (fun props => props.value.value == value)

/-- `felt.add x (felt.const 0)` → `x`. -/
def rightIdentityZeroAdd : Puddle.CompiledPattern OpCode :=
  (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := FeltType)
      let x ← Puddle.MatchProg.value type
      let zero ← constant type 0
      let _ ← Puddle.MatchProg.root (.felt .add) #[x, zero.res[0]!] #[type]
      return x)
    pure
    (fun x => (x : Puddle.Replacement OpCode))).compile

/-- `felt.mul x (felt.const 1)` → `x`. -/
def rightIdentityOneMul : Puddle.CompiledPattern OpCode :=
  (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := FeltType)
      let x ← Puddle.MatchProg.value type
      let one ← constant type 1
      let _ ← Puddle.MatchProg.root (.felt .mul) #[x, one.res[0]!] #[type]
      return x)
    pure
    (fun x => (x : Puddle.Replacement OpCode))).compile

/-- `felt.mul x (felt.const 0)` → the already-existing zero constant. -/
def rightZeroMul : Puddle.CompiledPattern OpCode :=
  (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := FeltType)
      let x ← Puddle.MatchProg.value type
      let zero ← constant type 0
      let _ ← Puddle.MatchProg.root (.felt .mul) #[x, zero.res[0]!] #[type]
      return zero.res[0]!)
    pure
    (fun x => (x : Puddle.Replacement OpCode))).compile

/-- `felt.neg (felt.neg x)` → `x`. -/
def negNegToSelf : Puddle.CompiledPattern OpCode :=
  (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := FeltType)
      let x ← Puddle.MatchProg.value type
      let inner ← Puddle.MatchProg.operation (.felt .neg) #[x] #[type]
      let _ ← Puddle.MatchProg.root (.felt .neg) #[inner.res[0]!] #[type]
      return x)
    pure
    (fun x => (x : Puddle.Replacement OpCode))).compile

/-- `felt.sub (felt.add x c) c` → `x`. -/
def addSubConstCancel : Puddle.CompiledPattern OpCode :=
  (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := FeltType)
      let x ← Puddle.MatchProg.value type
      let constant ← Puddle.MatchProg.operation (.felt .const) #[] #[type]
      let inner ← Puddle.MatchProg.operation (.felt .add) #[x, constant.res[0]!] #[type]
      let _ ← Puddle.MatchProg.root (.felt .sub)
        #[inner.res[0]!, constant.res[0]!] #[type]
      return x)
    pure
    (fun x => (x : Puddle.Replacement OpCode))).compile

/-- `felt.add (felt.sub x c) c` → `x`. -/
def subAddConstCancel : Puddle.CompiledPattern OpCode :=
  (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := FeltType)
      let x ← Puddle.MatchProg.value type
      let constant ← Puddle.MatchProg.operation (.felt .const) #[] #[type]
      let inner ← Puddle.MatchProg.operation (.felt .sub) #[x, constant.res[0]!] #[type]
      let _ ← Puddle.MatchProg.root (.felt .add)
        #[inner.res[0]!, constant.res[0]!] #[type]
      return x)
    pure
    (fun x => (x : Puddle.Replacement OpCode))).compile

/-- `felt.add (felt.add x c1) c2` → `felt.add x (felt.add c1 c2)`.
    The generic canonicalizer subsequently folds the new inner operation. -/
def reassociateConstantAdd : Puddle.CompiledPattern OpCode :=
  (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := FeltType)
      let x ← Puddle.MatchProg.value type
      let c1 ← Puddle.MatchProg.operation (.felt .const) #[] #[type]
      let inner ← Puddle.MatchProg.operation (.felt .add) #[x, c1.res[0]!] #[type]
      let c2 ← Puddle.MatchProg.operation (.felt .const) #[] #[type]
      let _ ← Puddle.MatchProg.root (.felt .add) #[inner.res[0]!, c2.res[0]!] #[type]
      return (type, x, c1.res[0]!, c2.res[0]!))
    (fun (type, x, c1, c2) => do
      let properties ← Puddle.CreateProg.property (.felt .add) ()
      let combined ← Puddle.CreateProg.operation (.felt .add) #[c1, c2] #[type] properties
      Puddle.CreateProg.operation (.felt .add) #[x, combined.res[0]!] #[type] properties)
    (fun result => (result : Puddle.Replacement OpCode))).compile

/-- `felt.mul (felt.mul x c1) c2` → `felt.mul x (felt.mul c1 c2)`.
    The generic canonicalizer subsequently folds the new inner operation. -/
def reassociateConstantMul : Puddle.CompiledPattern OpCode :=
  (Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := FeltType)
      let x ← Puddle.MatchProg.value type
      let c1 ← Puddle.MatchProg.operation (.felt .const) #[] #[type]
      let inner ← Puddle.MatchProg.operation (.felt .mul) #[x, c1.res[0]!] #[type]
      let c2 ← Puddle.MatchProg.operation (.felt .const) #[] #[type]
      let _ ← Puddle.MatchProg.root (.felt .mul) #[inner.res[0]!, c2.res[0]!] #[type]
      return (type, x, c1.res[0]!, c2.res[0]!))
    (fun (type, x, c1, c2) => do
      let properties ← Puddle.CreateProg.property (.felt .mul) ()
      let combined ← Puddle.CreateProg.operation (.felt .mul) #[c1, c2] #[type] properties
      Puddle.CreateProg.operation (.felt .mul) #[x, combined.res[0]!] #[type] properties)
    (fun result => (result : Puddle.Replacement OpCode))).compile

end PuddlePatterns

namespace LocalPatterns

private def zeroFor (ctx : WfIRContext OpCode) (value : ValuePtr) := do
  let resultType := value.getType! ctx.raw
  let .feltType fieldType := resultType.val | none
  let properties := FeltConstProperties.mk (FeltConstAttr.mk 0 fieldType)
  let (ctx, constant) ← WfRewriter.createOp! ctx (OpCode.felt .const) #[resultType] #[]
    #[] #[] properties none
  some (ctx, constant)

/-- `felt.sub x x` → `felt.const 0`. -/
private def selfSubtractionToZeroLocal : LocalRewritePattern OpCode := fun ctx op => do
  let some (lhs, rhs, _) := matchSub op ctx.raw | return (ctx, none)
  if lhs ≠ rhs then return (ctx, none)
  let (ctx, constant) ← zeroFor ctx lhs
  some (ctx, some (#[constant], #[(constant.getResult 0 : ValuePtr)]))

def selfSubtractionToZero : RewritePattern OpCode :=
  RewritePattern.fromLocalRewrite selfSubtractionToZeroLocal

/-- `felt.add x (felt.neg x)` → `felt.const 0`. -/
private def addNegToZeroLocal : LocalRewritePattern OpCode := fun ctx op => do
  let some (lhs, rhs, _) := matchAdd op ctx.raw | return (ctx, none)
  let some (inner, _) := matchNegFromValue rhs ctx.raw | return (ctx, none)
  if lhs ≠ inner then return (ctx, none)
  let (ctx, constant) ← zeroFor ctx lhs
  some (ctx, some (#[constant], #[(constant.getResult 0 : ValuePtr)]))

def addNegToZero : RewritePattern OpCode :=
  RewritePattern.fromLocalRewrite addNegToZeroLocal

end LocalPatterns

/-! # Pass implementation -/

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern
    #[ -- Add and subtraction simplifications.
       PuddlePatterns.rightIdentityZeroAdd.run, LocalPatterns.selfSubtractionToZero,
       PuddlePatterns.reassociateConstantAdd.run,
       -- Multiplication and negation simplifications.
       PuddlePatterns.rightIdentityOneMul.run, PuddlePatterns.rightZeroMul.run,
       LocalPatterns.addNegToZero, PuddlePatterns.negNegToSelf.run,
       -- Cancellation and reassociation.
       PuddlePatterns.addSubConstCancel.run, PuddlePatterns.subAddConstCancel.run,
       PuddlePatterns.reassociateConstantMul.run ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying felt-combine pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "felt-combine"
    description := "Felt-dialect identities, reassociation, and cancellation"
    run := fun _ => Combine.impl }

end Veir.FeltPass
