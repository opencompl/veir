import Veir.Parser.LLVMLexer

/-!
# AST and token grammar for a subset of textual LLVM IR

A fragment of the llir grammar (`llir/grammar`, `ll.tm`), cut down to what the
De Morgan examples use: function definitions with parameters, one or more basic
blocks, the binary bitwise instructions `xor`, `and`, `or`, and `ret`.

Constructor names follow the nonterminals of `ll.tm`
(`FuncDef`, `FuncHeader`, `Param`, `BasicBlock`, `XorInst`, `RetTerm`, ...).

The grammar is stated declaratively as relations between AST nodes and the
parser-facing token stream, i.e. the output of the lexer with trivia
(whitespace, comments) removed and without the final `Eof`.
A recursive-descent parser for this grammar is defined below.
-/

namespace Veir.LLVMParserProp

/-! ## AST -/

/-- `Type` in `ll.tm`, restricted to `IntType`. -/
inductive LLType where
  | int (width : Nat)
  deriving Repr, DecidableEq

/-- `Value` in `ll.tm`, restricted to local identifiers and `IntConst`. -/
inductive Value where
  | localIdent (name : String)
  | intConst (value : Int)
  deriving Repr, DecidableEq

/-- `TypeValue`: a type followed by a value, as in `ret i32 %result`. -/
structure TypeValue where
  ty : LLType
  val : Value
  deriving Repr, DecidableEq

/-- The binary instructions of the example (`XorInst`, `AndInst`, `OrInst`). -/
inductive BinOp where
  | xor | and | or
  deriving Repr, DecidableEq

/-- `ValueInstruction`, restricted to binary instructions: `op ty x, y`. -/
structure BinInst where
  op : BinOp
  ty : LLType
  lhs : Value
  rhs : Value
  deriving Repr, DecidableEq

/-- `LocalDefInst`: `%name = inst`. The fragment has no unnamed instructions. -/
structure Instruction where
  name : String
  inst : BinInst
  deriving Repr, DecidableEq

/-- `Terminator`, restricted to `RetTerm` with a value. -/
inductive Terminator where
  | ret (tv : TypeValue)
  deriving Repr, DecidableEq

/-- `BasicBlock`: a label, instructions, and a terminator. -/
structure BasicBlock where
  label : String
  insts : List Instruction
  term : Terminator
  deriving Repr, DecidableEq

/-- `Param`: a type and a named local. -/
structure Param where
  ty : LLType
  name : String
  deriving Repr, DecidableEq

/-- `FuncHeader`: return type, global name, and parameters. -/
structure FuncHeader where
  retType : LLType
  name : String
  params : List Param
  deriving Repr, DecidableEq

/-- `FuncDef`: `define` header `{` blocks `}`. -/
structure FuncDef where
  header : FuncHeader
  blocks : List BasicBlock
  deriving Repr, DecidableEq

/-- `Module`: a sequence of top-level entities, here only function definitions. -/
structure Module where
  funcs : List FuncDef
  deriving Repr, DecidableEq

/-! ## Token grammar

Each relation `X.Spells x ts` states that the token list `ts` is a derivation of
the AST node `x`. Soundness of a parser means it only returns `x` for `ts` with
`X.Spells x ts`; completeness means it returns some `x` whenever one exists. -/

inductive LLType.Spells : LLType → List Token → Prop where
  | int : LLType.Spells (.int w) [.intType w]

inductive Value.Spells : Value → List Token → Prop where
  | localIdent : Value.Spells (.localIdent n) [.LocalVar n]
  | intConst : Value.Spells (.intConst v) [.APSInt v]

inductive TypeValue.Spells : TypeValue → List Token → Prop where
  | mk : LLType.Spells τ ts₁ → Value.Spells v ts₂ →
      TypeValue.Spells ⟨τ, v⟩ (ts₁ ++ ts₂)

inductive BinOp.Spells : BinOp → List Token → Prop where
  | xor : BinOp.Spells .xor [.kw .xor]
  | and : BinOp.Spells .and [.kw .and]
  | or : BinOp.Spells .or [.kw .or]

inductive BinInst.Spells : BinInst → List Token → Prop where
  | mk : BinOp.Spells o tsOp → LLType.Spells τ tsTy →
      Value.Spells x tsL → Value.Spells y tsR →
      BinInst.Spells ⟨o, τ, x, y⟩ (tsOp ++ tsTy ++ tsL ++ [.punct .comma] ++ tsR)

inductive Instruction.Spells : Instruction → List Token → Prop where
  | mk : BinInst.Spells i ts →
      Instruction.Spells ⟨n, i⟩ (.LocalVar n :: .punct .equal :: ts)

inductive Terminator.Spells : Terminator → List Token → Prop where
  | ret : TypeValue.Spells v ts → Terminator.Spells (.ret v) (.kw .ret :: ts)

/-- A list of items, each spelled by `spells`, concatenated with `sep` between them. -/
inductive SepBy (spells : α → List Token → Prop) (sep : List Token) :
    List α → List Token → Prop where
  | nil : SepBy spells sep [] []
  | one : spells a ts → SepBy spells sep [a] ts
  | cons : spells a ts → SepBy spells sep (b :: as) tss →
      SepBy spells sep (a :: b :: as) (ts ++ sep ++ tss)

inductive BasicBlock.Spells : BasicBlock → List Token → Prop where
  | mk : SepBy Instruction.Spells [] is tsI → Terminator.Spells tm tsT →
      BasicBlock.Spells ⟨l, is, tm⟩ (.LabelStr l :: tsI ++ tsT)

inductive Param.Spells : Param → List Token → Prop where
  | mk : LLType.Spells τ ts → Param.Spells ⟨τ, n⟩ (ts ++ [.LocalVar n])

inductive FuncHeader.Spells : FuncHeader → List Token → Prop where
  | mk : LLType.Spells τ tsR → SepBy Param.Spells [.punct .comma] qs tsP →
      FuncHeader.Spells ⟨τ, n, qs⟩
        (tsR ++ .GlobalVar n :: .punct .lparen :: tsP ++ [.punct .rparen])

/-- LLVM requires a function definition to have at least one basic block. -/
inductive FuncDef.Spells : FuncDef → List Token → Prop where
  | mk : FuncHeader.Spells h tsH → blks ≠ [] → SepBy BasicBlock.Spells [] blks tsB →
      FuncDef.Spells ⟨h, blks⟩
        (.kw .define :: tsH ++ .punct .lbrace :: tsB ++ [.punct .rbrace])

inductive Module.Spells : Module → List Token → Prop where
  | mk : SepBy FuncDef.Spells [] fns ts → Module.Spells ⟨fns⟩ ts

/-! ## From characters to modules -/

/-- The parser-facing tokens of a lexed input: drop trivia and the final `Eof`. -/
def parserTokens (lexed : List (List Char × Token)) : List Token :=
  (lexed.map Prod.snd).filter fun t => !decide t.isTrivia && t != .Eof

/-- `src` denotes module `m`: it lexes, and its nontrivia tokens spell `m`. -/
def ParsesTo (src : List Char) (m : Module) : Prop :=
  ∃ lexed, Lexes src lexed ∧ Module.Spells m (parserTokens lexed)

/-! ## Recursive-descent parser -/

/-- Lexical failures, unexpected tokens (or end of input), and stalled parsers. -/
inductive ParserError where
  | lexical (error : TokenizationError)
  | unexpectedToken (expected : String) (actual : Option Token)
  | noProgress
  deriving Repr, DecidableEq

/-- A parser returns a value and the unconsumed tokens, or an error. -/
abbrev Parser := StateT (List Token) (Except ParserError)

/-- Consume a token with the expected shape. -/
def token (expected : String) (select : Token → Option α) : Parser α :=
  fun ts => match ts with
    | t :: rest => match select t with
      | some a => .ok (a, rest)
      | none => .error (.unexpectedToken expected (some t))
    | [] => .error (.unexpectedToken expected none)

def expect (t : Token) : Parser Unit :=
  token (reprStr t) fun t' => if t' = t then some () else none

def isLocalVar : Token → Prop
  | .LocalVar _ => True
  | _ => False

instance : DecidablePred isLocalVar :=
  fun t => by cases t <;> unfold isLocalVar <;> infer_instance

def isLabelStr : Token → Prop
  | .LabelStr _ => True
  | _ => False

instance : DecidablePred isLabelStr :=
  fun t => by cases t <;> unfold isLabelStr <;> infer_instance

/-- Whether the first token satisfies a predicate; false on empty input. -/
def startsWith (starts : Token → Prop) : List Token → Prop
  | [] => False
  | t :: _ => starts t

instance (starts : Token → Prop) [DecidablePred starts] : DecidablePred (startsWith starts) :=
  fun ts => match ts with
    | [] => inferInstanceAs (Decidable False)
    | t :: _ => inferInstanceAs (Decidable (starts t))

/-- Parse items while their first token matches; every item must consume input. -/
def manyWhile (starts : Token → Prop) [DecidablePred starts] (item : Parser α) : Parser (List α) :=
  fun ts => if startsWith starts ts then do
    let (a, rest) ← item ts
    if rest.length < ts.length then
      let (as, rest) ← manyWhile starts item rest
      return (a :: as, rest)
    else .error .noProgress
  else .ok ([], ts)
termination_by ts => ts.length

def parseType : Parser LLType :=
  token "integer type" fun | .intType w => some (.int w) | _ => none

def parseValue : Parser Value :=
  token "value" fun
    | .LocalVar n => some (.localIdent n)
    | .APSInt v => some (.intConst v)
    | _ => none

def parseLocalName : Parser String :=
  token "local name" fun | .LocalVar n => some n | _ => none

def parseTypeValue : Parser TypeValue :=
  return ⟨← parseType, ← parseValue⟩

def parseBinOp : Parser BinOp :=
  token "binary operator (xor, and, or)" fun
    | .kw .xor => some .xor
    | .kw .and => some .and
    | .kw .or => some .or
    | _ => none

def parseBinInst : Parser BinInst := do
  let op ← parseBinOp
  let ty ← parseType
  let lhs ← parseValue
  expect (.punct .comma)
  return ⟨op, ty, lhs, ← parseValue⟩

def parseInstruction : Parser Instruction := do
  let name ← parseLocalName
  expect (.punct .equal)
  return ⟨name, ← parseBinInst⟩

def parseTerminator : Parser Terminator := do
  expect (.kw .ret)
  return .ret (← parseTypeValue)

def parseBasicBlock : Parser BasicBlock := do
  let label ← token "block label" fun | .LabelStr n => some n | _ => none
  let insts ← manyWhile isLocalVar parseInstruction
  return ⟨label, insts, ← parseTerminator⟩

def parseParam : Parser Param :=
  return ⟨← parseType, ← parseLocalName⟩

def parseParams : Parser (List Param) := do
  if (← get).head? = some (.punct .rparen) then pure [] else do
    let first ← parseParam
    let rest ← manyWhile (· = .punct .comma) (expect (.punct .comma) *> parseParam)
    pure (first :: rest)

def parseFuncHeader : Parser FuncHeader := do
  let ty ← parseType
  let name ← token "global name" fun | .GlobalVar n => some n | _ => none
  expect (.punct .lparen)
  let params ← parseParams
  expect (.punct .rparen)
  return ⟨ty, name, params⟩

def parseFuncDef : Parser FuncDef := do
  expect (.kw .define)
  let header ← parseFuncHeader
  expect (.punct .lbrace)
  let first ← parseBasicBlock
  let rest ← manyWhile isLabelStr parseBasicBlock
  expect (.punct .rbrace)
  return ⟨header, first :: rest⟩

/-- Parse a complete trivia-free token stream without an EOF token. -/
def parseModule (ts : List Token) : Except ParserError Module := do
  let (funcs, rest) ← manyWhile (· = .kw .define) parseFuncDef ts
  match rest with
  | [] => return ⟨funcs⟩
  | t :: _ => .error (.unexpectedToken "function definition or end of input" (some t))

/-- Lex and parse textual LLVM IR in the supported grammar. -/
def parse (src : String) : Except ParserError Module := do
  let lexed ← (tokenizer src).mapError ParserError.lexical
  parseModule (parserTokens lexed)

/-! ## Correctness statements -/

theorem parserTokens_correct (lexed : List (List Char × Token)) (t : Token) :
    t ∈ parserTokens lexed ↔ t ∈ lexed.map Prod.snd ∧ ¬t.isTrivia ∧ t ≠ .Eof := by
  simp [parserTokens]

theorem ParsesTo_correct (src : List Char) (m : Module) :
    ParsesTo src m ↔ ∃ ts, Lexes src ts ∧ Module.Spells m (parserTokens ts) := Iff.rfl

theorem token_correct (expected : String) (select : Token → Option α)
    (ts rest : List Token) (a : α) :
    token expected select ts = .ok (a, rest) ↔
      ∃ t, ts = t :: rest ∧ select t = some a := by
  cases ts <;> simp [token] <;> split <;> simp_all <;> grind

theorem expect_correct (t : Token) (ts rest : List Token) :
    expect t ts = .ok ((), rest) ↔ ts = t :: rest := by
  simp [expect, token_correct]

/-- Repetition of spellings, including the stopping and progress conditions. -/
inductive Repeats (starts : Token → Prop) (spells : α → List Token → Prop) :
    List Token → List α → List Token → Prop where
  | stop : ¬ startsWith starts ts → Repeats starts spells ts [] ts
  | step : startsWith starts ts → (∃ pre, spells a pre ∧ ts = pre ++ next ∧ pre ≠ []) →
      Repeats starts spells next as rest → Repeats starts spells ts (a :: as) rest

theorem spells_progress (spells : α → List Token → Prop) (item : Parser α)
    (hp : ∀ ts rest a, item ts = .ok (a, rest) ↔ ∃ pre, spells a pre ∧ ts = pre ++ rest) :
    (∃ pre, spells a pre ∧ ts = pre ++ next ∧ pre ≠ []) ↔
      item ts = .ok (a, next) ∧ next.length < ts.length := by
  simp only [hp]
  constructor
  · rintro ⟨pre, h, rfl, hn⟩; exact ⟨⟨pre, h, rfl⟩, by simpa using List.length_pos_iff.mpr hn⟩
  · rintro ⟨⟨pre, h, rfl⟩, hl⟩; exact ⟨pre, h, rfl, by intro he; simp [he] at hl⟩

theorem repeats_iff (starts : Token → Prop) [DecidablePred starts]
    (spells : α → List Token → Prop) (item : Parser α)
    (hp : ∀ ts rest a, item ts = .ok (a, rest) ↔ ∃ pre, spells a pre ∧ ts = pre ++ rest)
    (ts rest : List Token) (as : List α) :
    Repeats starts spells ts as rest ↔
      if startsWith starts ts then ∃ a next tail, item ts = .ok (a, next) ∧
        next.length < ts.length ∧ Repeats starts spells next tail rest ∧ as = a :: tail
      else as = [] ∧ ts = rest := by
  split <;> constructor
  all_goals grind [Repeats, spells_progress spells item hp]

theorem except_map_ok (f : α → β) (e : Except ε α) (b : β) :
    f <$> e = .ok b ↔ ∃ a, e = .ok a ∧ f a = b := by
  cases e <;> simp [Functor.map, Except.map]

theorem manyWhile_correct (starts : Token → Prop) [DecidablePred starts]
    (spells : α → List Token → Prop) (item : Parser α)
    (hp : ∀ ts rest a, item ts = .ok (a, rest) ↔ ∃ pre, spells a pre ∧ ts = pre ++ rest)
    (ts rest : List Token) (as : List α) :
    manyWhile starts item ts = .ok (as, rest) ↔ Repeats starts spells ts as rest := by
  induction ts using manyWhile.induct starts generalizing as rest with
  | case1 ts hs ih =>
    rw [manyWhile, repeats_iff starts spells item hp]; simp only [hs, ↓reduceIte, Except.bind_eq_ok]
    constructor
    · rintro ⟨⟨a, next⟩, hi, h⟩; split at h <;> simp_all [except_map_ok]; grind
    · rintro ⟨a, next, tail, hi, hl, hr, rfl⟩
      exact ⟨(a, next), hi, by simp [hl, (ih next hl rest tail).mpr hr, Functor.map, Except.map]⟩
  | case2 ts hs => rw [manyWhile, repeats_iff starts spells item hp]; simp [hs, eq_comm]

theorem LLType.spells_iff (x : LLType) (ts : List Token) :
    LLType.Spells x ts ↔ ts = [match x with | .int w => .intType w] := by
  cases x <;> grind [LLType.Spells]

theorem Value.spells_iff (x : Value) (ts : List Token) :
    Value.Spells x ts ↔ ts = [match x with | .localIdent n => .LocalVar n | .intConst v => .APSInt v] := by
  grind [Value.Spells]

theorem BinOp.spells_iff (x : BinOp) (ts : List Token) :
    BinOp.Spells x ts ↔ ts = [match x with | .xor => .kw .xor | .and => .kw .and | .or => .kw .or] := by
  grind [BinOp.Spells]

theorem parseType_correct (ts rest : List Token) (x : LLType) :
    parseType ts = .ok (x, rest) ↔ ∃ pre, LLType.Spells x pre ∧ ts = pre ++ rest := by
  cases x <;> simp only [parseType, token_correct, LLType.spells_iff]
  all_goals grind [Token]

theorem parseValue_correct (ts rest : List Token) (x : Value) :
    parseValue ts = .ok (x, rest) ↔ ∃ pre, Value.Spells x pre ∧ ts = pre ++ rest := by
  cases x <;> simp only [parseValue, token_correct, Value.spells_iff]
  all_goals grind [Token]

theorem parseLocalName_correct (ts rest : List Token) (n : String) :
    parseLocalName ts = .ok (n, rest) ↔ ts = .LocalVar n :: rest := by
  simp only [parseLocalName, token_correct]
  grind [Token]

theorem bind_correct (p : Parser α) (f : α → Parser β) (ts rest : List Token) (b : β) :
    (p >>= f) ts = .ok (b, rest) ↔ ∃ a next, p ts = .ok (a, next) ∧ f a next = .ok (b, rest) := by
  change ((p ts) >>= _) = _ ↔ _
  simp [Except.bind_eq_ok]

theorem pure_correct (a b : α) (ts rest : List Token) :
    (pure a : Parser α) ts = .ok (b, rest) ↔ a = b ∧ ts = rest := by
  change Except.ok (a, ts) = Except.ok (b, rest) ↔ _
  simp

theorem map_correct (f : α → β) (p : Parser α) (ts rest : List Token) (b : β) :
    (f <$> p) ts = .ok (b, rest) ↔ ∃ a, p ts = .ok (a, rest) ∧ f a = b := by
  change (fun a => (f a.1, a.2)) <$> p ts = _ ↔ _
  simp [except_map_ok]

theorem expect_result (t : Token) (ts rest : List Token) (u : Unit) :
    expect t ts = .ok (u, rest) ↔ ts = t :: rest := by
  cases u; exact expect_correct t ts rest

theorem TypeValue.spells_iff (x : TypeValue) (ts : List Token) :
    TypeValue.Spells x ts ↔ ∃ a b, LLType.Spells x.ty a ∧ Value.Spells x.val b ∧ ts = a ++ b := by
  cases x <;> grind [TypeValue.Spells]

theorem parseTypeValue_correct (ts rest : List Token) (x : TypeValue) :
    parseTypeValue ts = .ok (x, rest) ↔ ∃ pre, TypeValue.Spells x pre ∧ ts = pre ++ rest := by
  cases x
  simp [parseTypeValue, bind_correct, map_correct, parseType_correct, parseValue_correct,
    TypeValue.spells_iff, LLType.spells_iff, Value.spells_iff, exists_and_left]
  simp [and_left_comm, and_comm]

theorem parseBinOp_correct (ts rest : List Token) (x : BinOp) :
    parseBinOp ts = .ok (x, rest) ↔ ∃ pre, BinOp.Spells x pre ∧ ts = pre ++ rest := by
  cases x <;> simp only [parseBinOp, token_correct, BinOp.spells_iff]
  all_goals grind [Token]

theorem BinInst.spells_iff (x : BinInst) (ts : List Token) :
    BinInst.Spells x ts ↔ ∃ a b c d, BinOp.Spells x.op a ∧ LLType.Spells x.ty b ∧
      Value.Spells x.lhs c ∧ Value.Spells x.rhs d ∧ ts = a ++ b ++ c ++ [.punct .comma] ++ d := by
  cases x <;> grind [BinInst.Spells]

theorem Instruction.spells_iff (x : Instruction) (ts : List Token) :
    Instruction.Spells x ts ↔ ∃ pre, BinInst.Spells x.inst pre ∧ ts = .LocalVar x.name :: .punct .equal :: pre := by
  cases x <;> grind [Instruction.Spells]

theorem Terminator.spells_iff (x : Terminator) (ts : List Token) :
    Terminator.Spells x ts ↔ ∃ tv pre, x = .ret tv ∧ TypeValue.Spells tv pre ∧ ts = .kw .ret :: pre := by
  grind [Terminator.Spells]

theorem Param.spells_iff (x : Param) (ts : List Token) :
    Param.Spells x ts ↔ ∃ pre, LLType.Spells x.ty pre ∧ ts = pre ++ [.LocalVar x.name] := by
  cases x <;> grind [Param.Spells]

theorem parseBinInst_correct (ts rest : List Token) (x : BinInst) :
    parseBinInst ts = .ok (x, rest) ↔ ∃ pre, BinInst.Spells x pre ∧ ts = pre ++ rest := by
  rcases x with ⟨op, ty, lhs, rhs⟩
  simp [parseBinInst, BinInst.spells_iff, bind_correct, map_correct, expect_result, parseType_correct,
    parseValue_correct, parseBinOp_correct, LLType.spells_iff, Value.spells_iff, BinOp.spells_iff,
    List.append_assoc, exists_and_left]
  simp [and_assoc, and_left_comm, and_comm]

theorem parseInstruction_correct (ts rest : List Token) (x : Instruction) :
    parseInstruction ts = .ok (x, rest) ↔ ∃ pre, Instruction.Spells x pre ∧ ts = pre ++ rest := by
  cases x
  simp [parseInstruction, Instruction.spells_iff, parseBinInst_correct, bind_correct,
    map_correct, expect_result, parseLocalName_correct]
  grind

theorem parseTerminator_correct (ts rest : List Token) (x : Terminator) :
    parseTerminator ts = .ok (x, rest) ↔ ∃ pre, Terminator.Spells x pre ∧ ts = pre ++ rest := by
  cases x
  simp [parseTerminator, Terminator.spells_iff, parseTypeValue_correct, bind_correct,
    map_correct, expect_result]
  grind

section Repetition
variable {α : Type} {R : α → List Token → Prop} {item : Parser α} {starts : Token → Prop} [DecidablePred starts]
  {ts rest pre tail : List Token} {a : α} {as : List α}

theorem SepBy.prepend (ha : R a pre) (h : SepBy R [] as tail) :
    SepBy R [] (a :: as) (pre ++ tail) := by
  cases h with
  | nil => simpa using SepBy.one ha
  | one hb => simpa using (SepBy.cons (sep := []) ha (.one hb))
  | cons hb hc => simpa using (SepBy.cons ha (.cons hb hc))

omit [DecidablePred starts] in
theorem Repeats.sound (h : Repeats starts R ts as rest) :
    ∃ pre, SepBy R [] as pre ∧ ts = pre ++ rest ∧ ¬ startsWith starts rest := by
  induction h with
  | stop hs => exact ⟨[], .nil, rfl, hs⟩
  | step hs hi hr ih =>
    obtain ⟨a, ha, rfl, _⟩ := hi; obtain ⟨b, hb, rfl, ht⟩ := ih
    exact ⟨a ++ b, hb.prepend ha, by simp, ht⟩

omit [DecidablePred starts] in
theorem Repeats.prepend
    (hs : ∀ a pre, R a pre → ∀ rest, startsWith starts (pre ++ rest))
    (ha : R a pre) (h : Repeats starts R ts as rest) :
    Repeats starts R (pre ++ ts) (a :: as) rest := by
  refine .step (hs _ _ ha _) ⟨pre, ha, rfl, ?_⟩ h
  intro he; simpa [he, startsWith] using hs _ _ ha []

omit [DecidablePred starts] in
theorem SepBy.repeats
    (hs : ∀ a pre, R a pre → ∀ rest, startsWith starts (pre ++ rest))
    (h : SepBy R [] as pre) (ht : ¬ startsWith starts rest) :
    Repeats starts R (pre ++ rest) as rest := by
  induction h with
  | nil => exact .stop ht
  | one ha => exact (Repeats.stop ht).prepend hs ha
  | cons ha hb ih => simpa [List.append_assoc] using ih.prepend hs ha

theorem manyWhile_spells (hp : ∀ ts rest a, item ts = .ok (a, rest) ↔
    ∃ pre, R a pre ∧ ts = pre ++ rest)
    (hs : ∀ a pre, R a pre → ∀ rest, startsWith starts (pre ++ rest)) :
    manyWhile starts item ts = .ok (as, rest) ↔
      ∃ pre, SepBy R [] as pre ∧ ts = pre ++ rest ∧ ¬ startsWith starts rest := by
  rw [manyWhile_correct starts R item hp]
  exact ⟨Repeats.sound, fun ⟨_, h, he, ht⟩ => he ▸ h.repeats hs ht⟩

end Repetition

theorem label_token (expected : String) (ts rest : List Token) (n : String) :
    token expected (fun | .LabelStr n => some n | _ => none) ts = .ok (n, rest) ↔
      ts = .LabelStr n :: rest := by
  rw [token_correct]; grind [Token]

theorem BasicBlock.spells_iff (x : BasicBlock) (ts : List Token) :
    BasicBlock.Spells x ts ↔ ∃ a b, SepBy Instruction.Spells [] x.insts a ∧
      Terminator.Spells x.term b ∧ ts = .LabelStr x.label :: a ++ b := by
  cases x <;> grind [BasicBlock.Spells]

theorem manyInstructions_correct (ts rest : List Token) (xs : List Instruction) :
    manyWhile isLocalVar parseInstruction ts = .ok (xs, rest) ↔
      ∃ pre, SepBy Instruction.Spells [] xs pre ∧ ts = pre ++ rest ∧
        ¬ startsWith isLocalVar rest := by
  apply manyWhile_spells parseInstruction_correct
  intro a pre h rest; cases h; trivial

theorem parseBasicBlock_correct (ts rest : List Token) (x : BasicBlock) :
    parseBasicBlock ts = .ok (x, rest) ↔ ∃ pre, BasicBlock.Spells x pre ∧ ts = pre ++ rest := by
  simp only [parseBasicBlock, bind_correct, pure_correct, label_token, manyInstructions_correct,
    parseTerminator_correct]
  constructor
  · rintro ⟨l, _, rfl, is, _, ⟨a, ha, rfl, _⟩, tm, _, ⟨b, hb, rfl⟩, rfl, rfl⟩
    exact ⟨_, .mk ha hb, by simp⟩
  · rintro ⟨pre, h, rfl⟩; obtain ⟨a, b, ha, hb, rfl⟩ := (BasicBlock.spells_iff _ _).mp h
    refine ⟨x.label, a ++ (b ++ rest), by simp [List.append_assoc], x.insts, b ++ rest,
      ⟨a, ha, rfl, ?_⟩, x.term, rest, ⟨b, hb, rfl⟩, (by cases x; rfl), rfl⟩
    obtain ⟨_, _, _, _, rfl⟩ := (Terminator.spells_iff _ _).mp hb; exact not_false

theorem parseParam_correct (ts rest : List Token) (x : Param) :
    parseParam ts = .ok (x, rest) ↔ ∃ pre, Param.Spells x pre ∧ ts = pre ++ rest := by
  rcases x with ⟨ty, name⟩
  simp [parseParam, Param.spells_iff, bind_correct, map_correct, parseLocalName_correct, parseType_correct,
    LLType.spells_iff]
  simp [and_comm, and_assoc]

section Separated
variable {α : Type} {R : α → List Token → Prop} {sep pre tail ts : List Token}
  {a : α} {as xs : List α}

theorem SepBy.join (ha : R a pre)
    (h : SepBy (fun a ts => ∃ pre, R a pre ∧ ts = sep ++ pre) [] as tail) :
    SepBy R sep (a :: as) (pre ++ tail) := by
  induction h generalizing a pre with
  | nil => simpa using SepBy.one ha
  | one hb => obtain ⟨_, hb, rfl⟩ := hb; simpa [List.append_assoc] using SepBy.cons ha (.one hb)
  | cons hb hc ih => obtain ⟨_, hb, rfl⟩ := hb; simpa [List.append_assoc] using SepBy.cons ha (ih hb)

theorem SepBy.split (h : SepBy R sep xs ts) : ∀ a as, xs = a :: as →
    ∃ pre tail, R a pre ∧ SepBy (fun a ts => ∃ pre, R a pre ∧ ts = sep ++ pre) [] as tail ∧ ts = pre ++ tail := by
  induction h with
  | nil => simp
  | one ha => intro a as he; cases he; exact ⟨_, [], ha, .nil, by simp⟩
  | cons ha hb ih =>
    intro a as he; cases he; obtain ⟨p, t, hp, ht, rfl⟩ := ih _ _ rfl
    exact ⟨_, sep ++ p ++ t, ha, ht.prepend ⟨p, hp, rfl⟩, by simp [List.append_assoc]⟩

theorem SepBy.cons_iff : SepBy R sep (a :: as) ts ↔
    ∃ pre tail, R a pre ∧ SepBy (fun a ts => ∃ pre, R a pre ∧ ts = sep ++ pre) [] as tail ∧ ts = pre ++ tail := by
  exact ⟨fun h => h.split _ _ rfl, fun ⟨_, _, hp, ht, he⟩ => he ▸ ht.join hp⟩

theorem SepBy.nil_iff : SepBy R sep [] ts ↔ ts = [] := by
  constructor <;> grind [SepBy]
end Separated

theorem global_token (expected : String) (ts rest : List Token) (n : String) :
    token expected (fun | .GlobalVar n => some n | _ => none) ts = .ok (n, rest) ↔
      ts = .GlobalVar n :: rest := by
  rw [token_correct]; grind [Token]

theorem commaParam_correct (ts rest : List Token) (p : Param) :
    (expect (.punct .comma) *> parseParam) ts = .ok (p, rest) ↔
      ∃ pre, (∃ q, Param.Spells p q ∧ pre = .punct .comma :: q) ∧ ts = pre ++ rest := by
  change (expect (.punct .comma) >>= fun _ => parseParam) ts = _ ↔ _
  simp [bind_correct, expect_result, parseParam_correct]
  grind

theorem manyParams_correct (ts rest : List Token) (ps : List Param) :
    manyWhile (· = .punct .comma) (expect (.punct .comma) *> parseParam) ts = .ok (ps, rest) ↔
      ∃ pre, SepBy (fun p ts => ∃ q, Param.Spells p q ∧ ts = .punct .comma :: q) [] ps pre ∧
        ts = pre ++ rest ∧ ¬ startsWith (· = .punct .comma) rest := by
  apply manyWhile_spells commaParam_correct
  rintro a pre ⟨q, h, rfl⟩ rest; rfl

theorem parseParams_sound (h : parseParams ts = .ok (ps, .punct .rparen :: rest)) :
    ∃ pre, SepBy Param.Spells [.punct .comma] ps pre ∧ ts = pre ++ .punct .rparen :: rest := by
  change (if ts.head? = some (.punct .rparen) then (pure [] : Parser (List Param)) else _) ts = _ at h
  split at h
  · cases h; exact ⟨[], .nil, rfl⟩
  · simp only [bind_correct, pure_correct, parseParam_correct, manyParams_correct] at h
    rcases h with ⟨a, _, ⟨p, hp, rfl⟩, as, _, ⟨t, ht, rfl, _⟩, rfl, rfl⟩
    exact ⟨p ++ t, ht.join hp, by simp⟩

theorem parseParams_step (hs : ts.head? ≠ some (.punct .rparen))
    (hp : parseParam ts = .ok (p, next))
    (hm : manyWhile (· = .punct .comma) (expect (.punct .comma) *> parseParam) next = .ok (ps, rest)) :
    parseParams ts = .ok (p :: ps, rest) := by
  change (if ts.head? = some (.punct .rparen) then (pure [] : Parser (List Param)) else _) ts = _
  rw [ite_eq_right hs]; change (parseParam ts >>= _) = _; rw [hp]
  change (fun ar : List Param × List Token => (p :: ar.1, ar.2)) <$> manyWhile _ _ next = _
  rw [hm]; rfl

theorem parseParams_complete (h : SepBy Param.Spells [.punct .comma] ps pre) :
    parseParams (pre ++ .punct .rparen :: rest) = .ok (ps, .punct .rparen :: rest) := by
  cases ps with
  | nil => cases h; rfl
  | cons p ps =>
    obtain ⟨a, b, ha, hb, rfl⟩ := h.split _ _ rfl
    have hs : (a ++ (b ++ .punct .rparen :: rest)).head? ≠ some (.punct .rparen) := by
      cases ha; cases ‹LLType.Spells _ _›; simp
    simp only [List.append_assoc]
    exact parseParams_step hs ((parseParam_correct _ _ _).mpr ⟨a, ha, rfl⟩)
      ((manyParams_correct _ _ _).mpr ⟨b, hb, rfl, by simp [startsWith]⟩)

theorem parseParams_correct (ts rest : List Token) (ps : List Param) :
    parseParams ts = .ok (ps, .punct .rparen :: rest) ↔
      ∃ pre, SepBy Param.Spells [.punct .comma] ps pre ∧ ts = pre ++ .punct .rparen :: rest := by
  exact ⟨parseParams_sound, fun ⟨_, h, he⟩ => he ▸ parseParams_complete h⟩

theorem FuncHeader.spells_iff (x : FuncHeader) (ts : List Token) :
    FuncHeader.Spells x ts ↔ ∃ a b, LLType.Spells x.retType a ∧
      SepBy Param.Spells [.punct .comma] x.params b ∧
      ts = a ++ .GlobalVar x.name :: .punct .lparen :: b ++ [.punct .rparen] := by
  cases x <;> grind [FuncHeader.Spells]

theorem parseFuncHeader_correct (ts rest : List Token) (x : FuncHeader) :
    parseFuncHeader ts = .ok (x, rest) ↔ ∃ pre, FuncHeader.Spells x pre ∧ ts = pre ++ rest := by
  simp only [parseFuncHeader, bind_correct, pure_correct, parseType_correct, global_token, expect_result, exists_const]
  constructor
  · rintro ⟨ty, _, ⟨a, ha, rfl⟩, name, _, rfl, _, rfl, ps, _, hp, _, rfl, rfl, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (parseParams_correct _ _ _).mp hp
    exact ⟨_, .mk ha hb, by simp⟩
  · rintro ⟨pre, h, rfl⟩; obtain ⟨a, b, ha, hb, rfl⟩ := (FuncHeader.spells_iff _ _).mp h
    exact ⟨x.retType, _, ⟨a, ha, by simp [List.append_assoc]⟩, x.name, _, rfl, _, rfl,
      x.params, _, parseParams_complete hb, rest, rfl, (by cases x; rfl), rfl⟩

theorem manyBlocks_correct (ts rest : List Token) (bs : List BasicBlock) :
    manyWhile isLabelStr parseBasicBlock ts = .ok (bs, rest) ↔
      ∃ pre, SepBy BasicBlock.Spells [] bs pre ∧ ts = pre ++ rest ∧
        ¬ startsWith isLabelStr rest := by
  apply manyWhile_spells parseBasicBlock_correct
  intro a pre h rest; cases h; trivial

theorem SepBy.cons_empty_iff {α : Type} {R : α → List Token → Prop} {a : α} {as : List α} {ts : List Token} :
    SepBy R [] (a :: as) ts ↔ ∃ pre tail, R a pre ∧ SepBy R [] as tail ∧ ts = pre ++ tail := by
  simpa using (SepBy.cons_iff (R := R) (sep := []) (a := a) (as := as) (ts := ts))

theorem FuncDef.spells_iff (x : FuncDef) (ts : List Token) :
    FuncDef.Spells x ts ↔ ∃ a b, FuncHeader.Spells x.header a ∧ x.blocks ≠ [] ∧
      SepBy BasicBlock.Spells [] x.blocks b ∧ ts = .kw .define :: a ++ .punct .lbrace :: b ++ [.punct .rbrace] := by
  cases x <;> grind [FuncDef.Spells]

theorem parseFuncDef_sound (h : parseFuncDef ts = .ok (x, rest)) :
    ∃ pre, FuncDef.Spells x pre ∧ ts = pre ++ rest := by
  simp only [parseFuncDef, bind_correct, pure_correct, expect_result, exists_const,
    parseFuncHeader_correct, parseBasicBlock_correct, manyBlocks_correct] at h
  rcases h with ⟨_, rfl, h, _, ⟨a, ha, rfl⟩, _, rfl, b, _, ⟨p, hp, rfl⟩,
    bs, _, ⟨q, hq, rfl, _⟩, _, rfl, rfl, rfl⟩
  exact ⟨_, .mk ha (by simp) (hq.prepend hp), by simp⟩

theorem parseFuncDef_complete (h : FuncDef.Spells x pre) :
    parseFuncDef (pre ++ rest) = .ok (x, rest) := by
  obtain ⟨a, b, ha, hn, hb, rfl⟩ := (FuncDef.spells_iff _ _).mp h
  rcases he : x.blocks with _ | ⟨first, bs⟩; · cases hn he
  obtain ⟨p, q, hp, hq, rfl⟩ := SepBy.cons_empty_iff.mp (he ▸ hb)
  simp only [parseFuncDef, bind_correct, pure_correct, expect_result, exists_const,
    parseFuncHeader_correct, parseBasicBlock_correct, manyBlocks_correct]
  exact ⟨_, rfl, x.header, _, ⟨a, ha, by simp [List.append_assoc]⟩, _, rfl,
    first, _, ⟨p, hp, rfl⟩, bs, .punct .rbrace :: rest, ⟨q, hq, rfl, not_false⟩,
    rest, rfl, (by cases x; simp_all), rfl⟩

theorem parseFuncDef_correct (ts rest : List Token) (x : FuncDef) :
    parseFuncDef ts = .ok (x, rest) ↔ ∃ pre, FuncDef.Spells x pre ∧ ts = pre ++ rest := by
  exact ⟨parseFuncDef_sound, fun ⟨_, h, he⟩ => he ▸ parseFuncDef_complete h⟩

theorem manyFuncs_correct (ts rest : List Token) (fs : List FuncDef) :
    manyWhile (· = .kw .define) parseFuncDef ts = .ok (fs, rest) ↔
      ∃ pre, SepBy FuncDef.Spells [] fs pre ∧ ts = pre ++ rest ∧
        ¬ startsWith (· = .kw .define) rest := by
  apply manyWhile_spells parseFuncDef_correct
  intro a pre h rest; cases h; trivial

theorem parseModule_correct (ts : List Token) (m : Module) :
    parseModule ts = .ok m ↔ Module.Spells m ts := by
  cases m
  simp only [parseModule, Except.bind_eq_ok]
  constructor
  · rintro ⟨⟨fs, rest⟩, hm, h⟩; cases rest <;> cases h
    obtain ⟨pre, hp, he, _⟩ := (manyFuncs_correct _ _ _).mp hm
    simp only [List.append_nil] at he; exact .mk (he.symm ▸ hp)
  · rintro ⟨h⟩; exact ⟨(_, []), (manyFuncs_correct _ _ _).mpr ⟨_, h, by simp, not_false⟩, rfl⟩

theorem parse_correct (src : String) (m : Module) :
    parse src = .ok m ↔ ParsesTo src.toList m := by
  simp only [parse, Except.bind_eq_ok, parseModule_correct, ParsesTo]
  constructor
  · rintro ⟨ts, ht, hm⟩; cases hl : tokenizer src <;> simp_all [Except.mapError, tokenizer_eq_ok_iff]
    exact ⟨ts, hl, hm⟩
  · rintro ⟨ts, ht, hm⟩; exact ⟨ts, by simp [tokenizer_success ht, Except.mapError], hm⟩

/-! ## Verified printing

The canonical printer separates tokens with spaces. Unlike the display-oriented
`ToString` instances, it reuses the lexer's verified token printer.
-/

def LLType.tokens : LLType → List Token
  | .int w => [.intType w]

def Value.tokens : Value → List Token
  | .localIdent n => [.LocalVar n]
  | .intConst v => [.APSInt v]

def TypeValue.tokens (v : TypeValue) : List Token := v.ty.tokens ++ v.val.tokens

def BinOp.tokens : BinOp → List Token
  | .xor => [.kw .xor]
  | .and => [.kw .and]
  | .or => [.kw .or]

def BinInst.tokens (i : BinInst) : List Token :=
  i.op.tokens ++ i.ty.tokens ++ i.lhs.tokens ++ [.punct .comma] ++ i.rhs.tokens

def Instruction.tokens (i : Instruction) : List Token :=
  .LocalVar i.name :: .punct .equal :: i.inst.tokens

def Terminator.tokens : Terminator → List Token
  | .ret v => .kw .ret :: v.tokens

def BasicBlock.tokens (b : BasicBlock) : List Token :=
  .LabelStr b.label :: b.insts.flatMap Instruction.tokens ++ b.term.tokens

def Param.tokens (p : Param) : List Token := p.ty.tokens ++ [.LocalVar p.name]

def FuncHeader.tokens (h : FuncHeader) : List Token :=
  h.retType.tokens ++ .GlobalVar h.name :: .punct .lparen ::
    ((h.params.map Param.tokens).intersperse [.punct .comma]).flatten ++ [.punct .rparen]

def FuncDef.tokens (f : FuncDef) : List Token :=
  .kw .define :: f.header.tokens ++ .punct .lbrace ::
    f.blocks.flatMap BasicBlock.tokens ++ [.punct .rbrace]

def Module.tokens (m : Module) : List Token := m.funcs.flatMap FuncDef.tokens

/-- Canonical textual LLVM IR, with a space after every token. -/
def Module.print (m : Module) : String := printTokens (m.tokens ++ [.Eof])

/-- Function bodies are nonempty and token payloads satisfy the lexer's name restrictions. -/
def Module.WellFormed (m : Module) : Prop :=
  (∀ f ∈ m.funcs, f.blocks ≠ []) ∧ IsValidTokenStream (m.tokens ++ [.Eof])

theorem LLType.spells_tokens (x : LLType) : LLType.Spells x x.tokens := by
  cases x; exact .int

theorem Value.spells_tokens (x : Value) : Value.Spells x x.tokens := by
  cases x <;> constructor

theorem TypeValue.spells_tokens (x : TypeValue) : TypeValue.Spells x x.tokens :=
  .mk x.ty.spells_tokens x.val.spells_tokens

theorem BinOp.spells_tokens (x : BinOp) : BinOp.Spells x x.tokens := by
  cases x <;> constructor

theorem BinInst.spells_tokens (x : BinInst) : BinInst.Spells x x.tokens :=
  .mk x.op.spells_tokens x.ty.spells_tokens x.lhs.spells_tokens x.rhs.spells_tokens

theorem Instruction.spells_tokens (x : Instruction) : Instruction.Spells x x.tokens :=
  .mk x.inst.spells_tokens

theorem Terminator.spells_tokens (x : Terminator) : Terminator.Spells x x.tokens := by
  cases x with | ret v => exact .ret v.spells_tokens

theorem SepBy.flatMap {α : Type} {R : α → List Token → Prop} {tokens : α → List Token}
    (xs : List α) (h : ∀ x ∈ xs, R x (tokens x)) : SepBy R [] xs (xs.flatMap tokens) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact (ih (by simp_all)).prepend (h x (by simp))

theorem BasicBlock.spells_tokens (x : BasicBlock) : BasicBlock.Spells x x.tokens :=
  .mk (SepBy.flatMap x.insts (fun i _ => i.spells_tokens)) x.term.spells_tokens

theorem Param.spells_tokens (x : Param) : Param.Spells x x.tokens :=
  .mk x.ty.spells_tokens

theorem SepBy.intersperse {α : Type} {R : α → List Token → Prop} {tokens : α → List Token}
    (xs : List α) (sep : List Token) (h : ∀ x ∈ xs, R x (tokens x)) :
    SepBy R sep xs ((xs.map tokens).intersperse sep).flatten := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    cases xs with
    | nil => simpa using SepBy.one (h x (by simp))
    | cons y ys => simpa using SepBy.cons (h x (by simp)) (ih (by simp_all))

theorem FuncHeader.spells_tokens (x : FuncHeader) : FuncHeader.Spells x x.tokens := by
  exact .mk x.retType.spells_tokens (SepBy.intersperse x.params _ (fun p _ => p.spells_tokens))

theorem FuncDef.spells_tokens (x : FuncDef) (h : x.blocks ≠ []) : FuncDef.Spells x x.tokens :=
  .mk x.header.spells_tokens h (SepBy.flatMap x.blocks (fun b _ => b.spells_tokens))

theorem Module.spells_tokens (m : Module) (h : ∀ f ∈ m.funcs, f.blocks ≠ []) :
    Module.Spells m m.tokens :=
  .mk (SepBy.flatMap m.funcs (fun f hf => f.spells_tokens (h f hf)))

theorem parserTokens_eq_significant (lexed : List (List Char × Token)) :
    parserTokens lexed = (significant lexed).filter (· != .Eof) := by
  simp [parserTokens, significant, List.filter_filter, Bool.and_comm]

theorem IsValidTokenStream.filter_eof (h : IsValidTokenStream ts) :
    ts.filter (· != .Eof) ++ [.Eof] = ts := by
  induction h with
  | eof => simp
  | @cons tok ts hv ht hn hs ih => simpa [hn] using congrArg (List.cons tok) ih

/-- Parsing a well-formed module's canonical textual representation recovers the AST. -/
theorem parse_print_round_trip (m : Module) (h : m.WellFormed) :
    parse m.print = .ok m := by
  obtain ⟨lexed, hl, he, -⟩ := h.2.print_lexes
  apply (parse_correct _ _).mpr
  refine ⟨lexed, hl, ?_⟩
  have ht := h.2.filter_eof
  rw [parserTokens_eq_significant, he]
  rw [(List.append_left_inj [Token.Eof]).mp ht]
  exact m.spells_tokens h.1

/--
info: define i32 @demorgan_or ( i32 %p , i32 %q ) { entry: %not_p = xor i32 %p , -1 %not_q = xor i32 %q , -1 %both_not = and i32 %not_p , %not_q %result = xor i32 %both_not , -1 ret i32 %result } define i32 @demorgan_and ( i32 %p , i32 %q ) { entry: %not_p = xor i32 %p , -1 %not_q = xor i32 %q , -1 %either_not = or i32 %not_p , %not_q %result = xor i32 %either_not , -1 ret i32 %result }
-/
#guard_msgs in
#eval match parse deMorganExample with
  | .ok m => IO.println $ Module.print $ m
  | .error e => IO.println (reprStr e)


end Veir.LLVMParserProp
