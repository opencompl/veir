import Veir.Parser.NameResolutionSketch
import Veir.Parser.DecidableInBounds
import Veir.Rewriter.WfRewriter
import Veir.OpCode
import Veir.Printer
import Veir.Dominance

namespace Veir.LLVMLowering

open LLVMParserProp NameResolutionSketch

abbrev LoweringError := String
abbrev LowerM := StateT (WfIRContext OpCode) (Except LoweringError)

def lowerType : LLType → TypeAttr
  | .int width => TypeAttr.of IntegerType (.signless width)

/-- Create an optionally attached operation, checking the construction helper's pointer preconditions. -/
def emit (opcode : Llvm) (types : Array TypeAttr) (operands : Array ValuePtr)
    (regions : Array RegionPtr) (properties : propertiesOf opcode) (block : BlockPtr) (insert : Bool := true) :
    LowerM OperationPtr := do
  let ip := if insert then some (InsertPoint.atEnd block) else none
  let ctx ← get
  if hoper : ∀ v ∈ operands, v.InBounds ctx.raw then
    if hregions : ∀ r ∈ regions, r.InBounds ctx.raw then
      if hins : ip.maybe InsertPoint.InBounds ctx.raw then
        let some (ctx', op) := WfRewriter.createOp ctx opcode types operands #[] regions
            properties ip hoper (by simp) hregions hins
          | throw "could not create operation"
        set ctx'
        return op
      else throw "invalid insertion block"
    else throw "invalid operation region"
  else throw "invalid operand"

/-- Create a detached function body with one entry block. -/
def createBody (types : Array TypeAttr) : LowerM (RegionPtr × BlockPtr) := do
  let some (ctx, region) := WfRewriter.createRegion (← get)
    | throw "could not create region"
  if hip : (some (BlockInsertPoint.atEnd region)).maybe BlockInsertPoint.InBounds ctx.raw then
    let some (ctx', block) := WfRewriter.createBlock ctx types (some (.atEnd region)) hip
      | throw "could not create entry block"
    set ctx'
    return (region, block)
  else throw "invalid body region"

/-- Resolve a reference through the complete result table, or materialise a literal. -/
def lowerValue (block : BlockPtr) (results : Array ValuePtr) (ty : LLType) :
    ResolvedValue → LowerM ValuePtr
  | .ref (.param i) => do
      let ctx ← get
      if i < block.getNumArguments! ctx.raw then
        return .blockArgument { block, index := i }
      else throw s!"parameter index {i} is out of bounds"
  | .ref (.inst i) =>
      match results[i]? with
      | some value => pure value
      | none => throw s!"instruction index {i} is out of bounds"
  | .intConst value => do
      let .int width := ty
      let op ← emit .mlir__constant #[lowerType ty] #[] #[]
        { value := .integer (IntegerAttr.ofInt value (.signless width)) } block
      return .opResult (op.getResult 0)

/-- Allocate an instruction's result before resolving any operands. -/
def lowerInst (block : BlockPtr) : ResolvedAST → LowerM OperationPtr
  | .bin op ty _ _ =>
      match op with
      | .and => emit .and #[lowerType ty] #[] #[] () block false
      | .or => emit .or #[lowerType ty] #[] #[] { disjoint := false } block false
      | .xor => emit .xor #[lowerType ty] #[] #[] () block false

/-- Allocate all definitions, then wire operands and insert each instruction after its constants. -/
def lowerInsts (block : BlockPtr) (insts : List ResolvedAST) : LowerM (Array ValuePtr) := do
  let ops ← insts.toArray.mapM (lowerInst block)
  let results := ops.map (fun op => ValuePtr.opResult (op.getResult 0))
  for (inst, op) in insts.zip ops.toList do
    let .bin _ ty lhs rhs := inst
    for operand in [lhs, rhs] do
      let v ← lowerValue block results ty operand
      let ctx ← get
      if ho : op.InBounds ctx.raw then
        if hv : v.InBounds ctx.raw then
          set (WfRewriter.pushOperand ctx op v ho hv)
        else throw "invalid operand"
      else throw "invalid instruction"
    let ctx ← get
    if ho : op.InBounds ctx.raw then
      if hb : (InsertPoint.atEnd block).InBounds ctx.raw then
        let some ctx' := WfRewriter.insertOp ctx op (.atEnd block) ho hb
          | throw "could not insert instruction"
        set ctx'
      else throw "invalid insertion block"
    else throw "invalid instruction"
  return results

def lowerFunction (moduleBlock : BlockPtr) (f : ResolvedFunction) : LowerM OperationPtr := do
  let inputs := f.header.params.toArray.map (lowerType ·.ty)
  let output := lowerType f.header.retType
  let (region, block) ← createBody inputs
  let results ← lowerInsts block f.insts
  let value ← lowerValue block results f.header.retType f.result
  let _ ← emit .return #[] #[value] #[] () block
  emit .func #[] #[] #[region]
    { sym_name := ⟨f.header.name.toUTF8⟩
      function_type := { inputs := inputs.map Subtype.val, outputs := #[output.val] }
      extra := .empty } moduleBlock

/-- Prototype lowering of the resolved single-block integer fragment.
Supports forward references and rejects undefined references; LLVM validity is checked separately. -/
def lowerModule (m : ResolvedModule) :
    Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let some (ctx, root) := WfIRContext.create OpCode
    | throw "could not create module"
  let some block := (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
    | throw "module has no body block"
  let ((), ctx') ← (m.funcs.forM (fun f => do
    let _ ← lowerFunction block f)).run ctx
  return (ctx', root)

/-! Declarative specification of the final graph. Each instruction lowers to a tile containing
its operand constants followed by its defining op. Local names and allocation IDs are ignored.
This specifies the single-block representation, not full LLVM verification. -/

section Specification

variable (ctx : WfIRContext OpCode)

/-- Equality of observable operation fields, excluding allocation and use-list links. -/
def MatchesOp (op : OperationPtr)
    {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
    (opcode : Dialect) (types : Array TypeAttr) (operands : Array ValuePtr)
    (regions : Array RegionPtr) (properties : propertiesOf opcode) : Prop :=
  op.InBounds ctx.raw ∧ op.getProperties! ctx.raw opcode = properties ∧
  (op.getOpType! ctx.raw, op.getResultTypes! ctx.raw, op.getOperands! ctx.raw,
    op.getRegions! ctx.raw, op.getNumSuccessors! ctx.raw, op.getAttributes! ctx.raw) =
  (ofDialect OpCode opcode, types, operands, regions, 0, DictionaryAttr.empty)

def binOpcode : BinOp → Llvm
  | .and => .and
  | .or => .or
  | .xor => .xor

abbrev ValueMap := ValueId → Option ValuePtr

/-- `OperandTile values ty val v cs`: `val` denotes `v`, and `cs` are the ops materialised
for it: none for a reference, one `mlir.constant` for a literal. -/
def OperandTile (values : ValueMap) : LLType → ResolvedValue → ValuePtr → List OperationPtr → Prop
  | _, .ref id, v, cs => values id = some v ∧ cs = []
  | .int w, .intConst n, v, cs => ∃ c, cs = [c] ∧ v = .opResult (c.getResult 0) ∧
      MatchesOp ctx c Llvm.mlir__constant #[lowerType (.int w)] #[] #[]
        (LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt n (.signless w))))

/-- `LowersInstTile values id inst tile`: `inst`, named `id`, lowers to exactly the ops `tile`:
the constants of its operands, left to right, followed by its defining op. -/
def LowersInstTile (values : ValueMap) (id : ValueId) : ResolvedAST → List OperationPtr → Prop
  | .bin opc ty l r, tile => ∃ vl vr cl cr op, tile = cl ++ cr ++ [op] ∧
      OperandTile ctx values ty l vl cl ∧ OperandTile ctx values ty r vr cr ∧
      values id = some (.opResult (op.getResult 0)) ∧
      MatchesOp ctx op (binOpcode opc) #[lowerType ty] #[vl, vr] #[] default

/-- All references name existing definitions. Each instruction lowers to a tile of ops,
and the body block is exactly the tiles, then
the return value's constants, then the return. This fixes operation order, not dominance. -/
def LowersFunctionTiles (f : ResolvedFunction) (op : OperationPtr) : Prop :=
  ValidResolvedFunction f ∧
  ∃ region block, ∃ tiles : List (List OperationPtr), ∃ cs ret v, ∃ values : ValueMap,
    MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
        { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
          outputs := #[(lowerType f.header.retType).val] } .empty) ∧
    region.BlockChain ctx.raw #[block] ∧
    block.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty) ∧
    (∀ i, values (.param i) = (block.getArguments! ctx.raw)[i]?) ∧
    ResolvesList (fun (inst, i) => LowersInstTile ctx values (.inst i) inst) f.insts.zipIdx tiles ∧
    OperandTile ctx values f.header.retType f.result v cs ∧
    MatchesOp ctx ret Llvm.return #[] #[v] #[] () ∧
    block.OpChain ctx.raw (tiles.flatten ++ cs ++ [ret]).toArray


/-- Only the module reachable from the root is specified;  We don't require Dominance -/
def LowersModule (m : ResolvedModule) (root : OperationPtr) : Prop :=
  ∃ (region : RegionPtr) (block : BlockPtr) (funcs : List OperationPtr),
    MatchesOp ctx root Builtin.module #[] #[] #[region] default ∧
    region.BlockChain ctx.raw #[block] ∧
    block.OpChain ctx.raw funcs.toArray ∧
    root.getParent! ctx.raw = none ∧
    block.getArgumentTypes! ctx.raw = #[] ∧ ResolvesList (LowersFunctionTiles ctx) m.funcs funcs



end Specification

/--
info: "builtin.module"() ({
  ^2():
    "llvm.func"() <{"function_type" = !llvm.func<i32 (i32, i32)>, "sym_name" = "demorgan_or"}> ({
      ^4(%arg4_0 : i32, %arg4_1 : i32):
        %9 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %5 = "llvm.xor"(%arg4_0, %9) : (i32, i32) -> i32
        %10 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %6 = "llvm.xor"(%arg4_1, %10) : (i32, i32) -> i32
        %7 = "llvm.and"(%5, %6) : (i32, i32) -> i32
        %11 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %8 = "llvm.xor"(%7, %11) : (i32, i32) -> i32
        "llvm.return"(%8) : (i32) -> ()
    }) : () -> ()
    "llvm.func"() <{"function_type" = !llvm.func<i32 (i32, i32)>, "sym_name" = "demorgan_and"}> ({
      ^15(%arg15_0 : i32, %arg15_1 : i32):
        %20 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %16 = "llvm.xor"(%arg15_0, %20) : (i32, i32) -> i32
        %21 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %17 = "llvm.xor"(%arg15_1, %21) : (i32, i32) -> i32
        %18 = "llvm.or"(%16, %17) : (i32, i32) -> i32
        %22 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %19 = "llvm.xor"(%18, %22) : (i32, i32) -> i32
        "llvm.return"(%19) : (i32) -> ()
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in
#eval show IO Unit from do
  match lowerModule resolvedDeMorganModule with
  | .error error => throw (IO.userError error)
  | .ok (ctx, root) => Printer.printModule ctx.raw root

#eval (lowerModule resolvedDeMorganModule).map (·.1.raw)

def equivalent_modulo_renaming_rearranging (ctx1 : WfIRContext OpCode) (root1 : OperationPtr)
    (ctx2 : WfIRContext OpCode) (root2 : OperationPtr) : Prop :=
  sorry

theorem lowerModule_sound : lowerModule m = .ok (ctx, root) → LowersModule ctx m root := sorry
theorem lowerModule_complete : LowersModule ctx m root  → ∃ ctx2 root2, lowerModule m = .ok (ctx2, root2) ∧
  equivalent_modulo_renaming_rearranging ctx root ctx2 root2 := sorry

end Veir.LLVMLowering
