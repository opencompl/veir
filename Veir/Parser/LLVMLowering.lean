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

/-- Append an operation, checking the construction helper's pointer preconditions. -/
def emit (opcode : Llvm) (types : Array TypeAttr) (operands : Array ValuePtr)
    (regions : Array RegionPtr) (properties : propertiesOf opcode) (block : BlockPtr) :
    LowerM OperationPtr := do
  let ctx ← get
  if hoper : ∀ v ∈ operands, v.InBounds ctx.raw then
    if hregions : ∀ r ∈ regions, r.InBounds ctx.raw then
      if hins : (some (InsertPoint.atEnd block)).maybe InsertPoint.InBounds ctx.raw then
        let some (ctx', op) := WfRewriter.createOp ctx opcode types operands #[] regions
            properties (some (.atEnd block)) hoper (by simp) hregions hins
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

/-- Earlier instruction results and entry arguments are the available SSA values. -/
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
      | none => throw s!"instruction {i} is unavailable (forward or invalid reference)"
  | .intConst value => do
      let .int width := ty
      let op ← emit .mlir__constant #[lowerType ty] #[] #[]
        { value := .integer (IntegerAttr.ofInt value (.signless width)) } block
      return .opResult (op.getResult 0)

def lowerFunction (moduleBlock : BlockPtr) (f : ResolvedFunction) : LowerM Unit := do
  let inputs := f.header.params.toArray.map (lowerType ·.ty)
  let output := lowerType f.header.retType
  let (region, block) ← createBody inputs
  let mut results := #[]
  for inst in f.insts do
    let .bin op ty lhs rhs := inst
    let lhs ← lowerValue block results ty lhs
    let rhs ← lowerValue block results ty rhs
    let result ← match op with
      | .and => emit .and #[lowerType ty] #[lhs, rhs] #[] () block
      | .or => emit .or #[lowerType ty] #[lhs, rhs] #[] { disjoint := false } block
      | .xor => emit .xor #[lowerType ty] #[lhs, rhs] #[] () block
    results := results.push (.opResult (result.getResult 0))
  let value ← lowerValue block results f.header.retType f.result
  let _ ← emit .return #[] #[value] #[] () block
  let _ ← emit .func #[] #[] #[region]
    { sym_name := ⟨f.header.name.toUTF8⟩
      function_type := { inputs := inputs.map Subtype.val, outputs := #[output.val] }
      extra := .empty } moduleBlock
  return ()

/-- Prototype lowering of the resolved single-block integer fragment.
Rejects unavailable references; full LLVM type and symbol verification is separate. -/
def lowerModule (m : ResolvedModule) :
    Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let some (ctx, root) := WfIRContext.create OpCode
    | throw "could not create module"
  let some block := (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
    | throw "module has no body block"
  let ((), ctx') ← (m.funcs.forM (lowerFunction block)).run ctx
  return (ctx', root)

/-! Declarative specification of the final graph. Each instruction has one defining op, kept in
order; a literal may be any earlier constant. Local names and allocation IDs are ignored.
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

/-- The value an operand denotes, given each instruction's defining op. -/
def Denotes (args : Array ValuePtr) (defs : List OperationPtr) :
    LLType → ResolvedValue → ValuePtr → Prop
  | _, .ref (.param i), v => args[i]? = some v
  | _, .ref (.inst j), v => ∃ op, defs[j]? = some op ∧ v = .opResult (op.getResult 0)
  | .int w, .intConst n, v => ∃ c, v = .opResult (c.getResult 0) ∧
      MatchesOp ctx c Llvm.mlir__constant #[lowerType (.int w)] #[] #[]
        (LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt n (.signless w))))

def binOpcode : BinOp → Llvm
  | .and => .and
  | .or => .or
  | .xor => .xor

def LowersInst (args : Array ValuePtr) (defs : List OperationPtr) :
    ResolvedAST → OperationPtr → Prop
  | .bin opc ty l r, op => ∃ vl vr,
      Denotes ctx args defs ty l vl ∧ Denotes ctx args defs ty r vr ∧
      MatchesOp ctx op (binOpcode opc) #[lowerType ty] #[vl, vr] #[] default

/-- Instruction ops in order, then the return; constants may appear anywhere before their uses. -/
def LowersFunction (f : ResolvedFunction) (op : OperationPtr) : Prop :=
  ∃ region block, ∃ ops : List OperationPtr, ∃ defs ret,
    MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
        { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
          outputs := #[(lowerType f.header.retType).val] } .empty) ∧
    region.BlockChain ctx.raw #[block] ∧ block.OpChain ctx.raw ops.toArray ∧
    block.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty) ∧
    ResolvesList (LowersInst ctx (block.getArguments! ctx.raw) defs) f.insts defs ∧
    (∃ v, Denotes ctx (block.getArguments! ctx.raw) defs f.header.retType f.result v ∧
      MatchesOp ctx ret Llvm.return #[] #[v] #[] ()) ∧
    ops.filter (·.getOpType! ctx.raw != ofDialect OpCode Llvm.mlir__constant) = defs ++ [ret]

/-- Only the module reachable from the root is specified; `Dom` orders definitions before uses. -/
def LowersModule (m : ResolvedModule) (root : OperationPtr) : Prop :=
  ∃ (region : RegionPtr) (block : BlockPtr) (funcs : List OperationPtr),
    MatchesOp ctx root Builtin.module #[] #[] #[region] default ∧
    root.getParent! ctx.raw = none ∧ ctx.Dom (.operation root) ∧
    block.getArgumentTypes! ctx.raw = #[] ∧ ResolvesList (LowersFunction ctx) m.funcs funcs

end Specification

/--
info: "builtin.module"() ({
  ^2():
    "llvm.func"() <{"function_type" = !llvm.func<i32 (i32, i32)>, "sym_name" = "demorgan_or"}> ({
      ^4(%arg4_0 : i32, %arg4_1 : i32):
        %5 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %6 = "llvm.xor"(%arg4_0, %5) : (i32, i32) -> i32
        %7 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %8 = "llvm.xor"(%arg4_1, %7) : (i32, i32) -> i32
        %9 = "llvm.and"(%6, %8) : (i32, i32) -> i32
        %10 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %11 = "llvm.xor"(%9, %10) : (i32, i32) -> i32
        "llvm.return"(%11) : (i32) -> ()
    }) : () -> ()
    "llvm.func"() <{"function_type" = !llvm.func<i32 (i32, i32)>, "sym_name" = "demorgan_and"}> ({
      ^15(%arg15_0 : i32, %arg15_1 : i32):
        %16 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %17 = "llvm.xor"(%arg15_0, %16) : (i32, i32) -> i32
        %18 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %19 = "llvm.xor"(%arg15_1, %18) : (i32, i32) -> i32
        %20 = "llvm.or"(%17, %19) : (i32, i32) -> i32
        %21 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %22 = "llvm.xor"(%20, %21) : (i32, i32) -> i32
        "llvm.return"(%22) : (i32) -> ()
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in
#eval show IO Unit from do
  match lowerModule resolvedDeMorganModule with
  | .error error => throw (IO.userError error)
  | .ok (ctx, root) => Printer.printModule ctx.raw root
example : False := by
  let x : Except LoweringError (WfIRContext OpCode × OperationPtr)  := lowerModule resolvedDeMorganModule

  sorry


-- root = op1, nextID = 25
-- -- regions
-- rgn0:  parent=op1  first=blk2  last=blk2
-- rgn3:  parent=op13 first=blk4  last=blk4
-- rgn14: parent=op24 first=blk15 last=blk15
-- -- blocks
-- blk2:  parent=rgn0  firstOp=op13 lastOp=op24 args=0
-- blk4:  parent=rgn3  firstOp=op5  lastOp=op12 args=2
-- blk15: parent=rgn14 firstOp=op16 lastOp=op23 args=2
-- -- operations
-- op1:  builtin.module     parent=·    prev=·    next=·    regions=[0]
-- op5:  llvm.mlir.constant parent=blk4 prev=·    next=op6  operands=[]                        firstUse=op6
-- op6:  llvm.xor           parent=blk4 prev=op5  next=op7  operands=[arg(blk4#0), res(op5#0)] firstUse=op9
-- op7:  llvm.mlir.constant parent=blk4 prev=op6  next=op8  operands=[]                        firstUse=op8
-- op8:  llvm.xor           parent=blk4 prev=op7  next=op9  operands=[arg(blk4#1), res(op7#0)] firstUse=op9
-- op9:  llvm.and           parent=blk4 prev=op8  next=op10 operands=[res(op6#0), res(op8#0)]  firstUse=op11
-- op10: llvm.mlir.constant parent=blk4 prev=op9  next=op11 operands=[]                        firstUse=op11
-- op11: llvm.xor           parent=blk4 prev=op10 next=op12 operands=[res(op9#0), res(op10#0)] firstUse=op12
-- op12: llvm.return        parent=blk4 prev=op11 next=·    operands=[res(op11#0)]
-- op13: llvm.func          parent=blk2 prev=·    next=op24 regions=[3]
-- op16 … op23: the same shape for demorgan_and, with llvm.or at op20
-- op24: llvm.func          parent=blk2 prev=op13 next=·    regions=[14]

#eval (lowerModule resolvedDeMorganModule).map (·.1.raw)

 end Veir.LLVMLowering
