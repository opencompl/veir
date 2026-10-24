import Veir.GlobalOpInfo
import Veir.IR.WellFormed


/-!
# Proof sketch for Essay 1: a verified LLVM IR parser for VeIR

The parser and its main theorems are sketches; the token relation below has
explicit spelling rules.
The parser's output is a VeIR program: a well-formed `IRContext` over VeIR's
`OpCode` (which includes the LLVM dialect), together with the top-level
`builtin.module` operation.
-/

namespace Veir.LLVMParser

open Veir

/-! ## Tokens

Tokens needed for the two De Morgan functions in the example. Whitespace and
comments are represented explicitly in the lexical specification. -/

/-- Keywords are data: adding one means a constructor plus a spelling line. -/
inductive Keyword where
  | define | ret | xor | and | or
  deriving Repr, DecidableEq

def Keyword.all : List Keyword := [.define, .ret, .xor, .and, .or]

def Keyword.spelling : Keyword → String
  | .define => "define" | .ret => "ret" | .xor => "xor" | .and => "and" | .or => "or"

inductive Punct where
  | equal | comma | lbrace | rbrace | lparen | rparen
  deriving Repr, DecidableEq

def Punct.all : List Punct := [.equal, .comma, .lbrace, .rbrace, .lparen, .rparen]

def Punct.char : Punct → Char
  | .equal => '=' | .comma => ',' | .lbrace => '{' | .rbrace => '}' | .lparen => '(' | .rparen => ')'

theorem Keyword.mem_all (k : Keyword) : k ∈ Keyword.all := by cases k <;> decide
theorem Punct.mem_all (p : Punct) : p ∈ Punct.all := by cases p <;> decide

/-- Looking up a spelling finds the keyword it spells; proved once for all keywords. -/
theorem Keyword.find_spelling :
    ∀ k ∈ Keyword.all, Keyword.all.find? (·.spelling == k.spelling) = some k := by decide

theorem Punct.find_char :
    ∀ p ∈ Punct.all, Punct.all.find? (·.char == p.char) = some p := by decide

inductive Token : Type where
  | Eof
  | ws
  | comment
  | punct (p : Punct)
  | kw (k : Keyword)
  | intType (width : Nat)
  | LabelStr (name : String)
  | GlobalVar (name : String)
  | LocalVar (name : String)
  | APSInt (value : Int)
  deriving Repr, DecidableEq

/-- Skeleton tree from the first pass: names unresolved, phi nodes still present. -/
def LLVMModule : Type := sorry

/-- A VeIR program: a well-formed context plus its top-level module operation. -/
abbrev VeIRModule : Type := WfIRContext OpCode × OperationPtr

/-! ## Declarative specification -/

/-- List membership with the position of the occurrence as data. -/
private inductive Member (a : α) : List α → Type where
  | head : Member a (a :: xs)
  | tail : Member a xs → Member a (b :: xs)

/-- Every element satisfies a type-valued condition. -/
private inductive All (P : α → Type) : List α → Type where
  | nil : All P []
  | cons : P x → All P xs → All P (x :: xs)

private def asciiAlpha (c : Char) : Type :=
  Member c "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toList

private def isDigit (c : Char) : Type :=
  Member c "0123456789".toList

inductive digitNum : Char → Nat →  Type where
  | zero : digitNum '0' 0
  | one : digitNum '1' 1
  | two : digitNum '2' 2
  | three : digitNum '3' 3
  | four : digitNum '4' 4
  | five : digitNum '5' 5
  | six : digitNum '6' 6
  | seven : digitNum '7' 7
  | eight : digitNum '8' 8
  | nine : digitNum '9' 9

inductive digitsNum : String → Nat →  Type where
  | singleDigit : digitNum c n → digitsNum c.toString n
  | digits : digitsNum c n → digitNum d m → digitsNum (String.append c d.toString) (10 * n + m)

private def nameStart (c : Char) : Type :=
  asciiAlpha c ⊕ Member c "-$._".toList

private def nameChar (c : Char) : Type :=
  nameStart c ⊕ isDigit c

def decides (T : Type) : Type := T ⊕ (T → Empty)


def toListDecide (x : α) (xs : List α) [DecidableEq α]: decides (Member x xs)  :=
  match xs with
  | [] => .inr (fun m => by cases m)
  | y :: ys =>  if h : x = y then
    .inl (h ▸ .head)
  else
    match toListDecide x ys with
    | .inl m => .inl (.tail m)
    | .inr nm => .inr (fun m => match m with
      | .head => by simp only [not_true_eq_false] at h
      | .tail m' => nm m')

def plusDecide (x : decides A) (y : decides B) : decides (A ⊕ B) :=
  match x with
  | .inl xa => .inl (.inl xa)
  | .inr xna => match y with
    | .inl yb => .inl $ .inr yb
    | .inr ynb => .inr (Sum.elim xna ynb)

def nameStartDecide (c : Char) : decides (nameStart c) :=
  plusDecide (toListDecide c "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toList) (toListDecide c "-$._".toList)


def nameCharDecide (c : Char) : decides (nameChar c) :=
  plusDecide (nameStartDecide c) (toListDecide c "0123456789".toList)

private def bareName (s : String) : Type :=
  match s.toList with
  | [] => Empty
  | c :: cs => nameStart c × All nameChar cs

private def labelName (s : String) : Type :=
  PLift (s ≠ "") × All nameChar s.toList

private def digits (s : String) : Type :=
  PLift (s ≠ "") × All isDigit s.toList

inductive decimalInteger : String → Int → Type where
  | positive : digitsNum s n →  decimalInteger s n
  | negative  : digitsNum s n →  decimalInteger ("-" ++ s) (-n)

def noLinebreaks (s : String) : Type :=
  All (fun c => (PLift (c = '\n') ⊕ PLift (c = '\r')) → Empty) s.toList
/-- Tokens spelled by a maximal run of name characters: keywords and `iN` types. -/
inductive WordToken : String → Token → Type where
  | keyword (k : Keyword) : WordToken k.spelling (.kw k)
  | intType {s : String} {n : Nat} : digitsNum s n → n ≠ 0 → WordToken ("i" ++ s) (.intType n)

def isWs (c : Char) : Type :=
  Member c " \t\n\r".toList

def decideWS (c : Char) : decides (isWs c) :=
  toListDecide c " \t\n\r".toList

/-- Spellings of the tokens in the example; boundaries belong to `Lexes`. -/
inductive TokenRepresentation : String → Token → Type where
  | eof : TokenRepresentation "" .Eof
  | ws {s : String} : PLift (s ≠ "") →
      All isWs s.toList →
      TokenRepresentation s .ws
  | comment {line : String} {endChar : Char}
     :  noLinebreaks line → Member endChar "\n\r".toList →
      TokenRepresentation (";" ++ line ++ String.singleton endChar) .comment
  | commentEof {line : String} :
      noLinebreaks line →
      TokenRepresentation (";" ++ line) .comment
  | punct (p : Punct) : TokenRepresentation (String.singleton p.char) (.punct p)
  | word {w : String} {tok : Token} : WordToken w tok → TokenRepresentation w tok
  | label (name : String) : labelName name × (digits name → Empty) →
      TokenRepresentation (name ++ ":") (.LabelStr name)
  | global (name : String) : bareName name →
      TokenRepresentation ("@" ++ name) (.GlobalVar name)
  | local (name : String) : bareName name →
      TokenRepresentation ("%" ++ name) (.LocalVar name)
  | integer {s : String} {value : Int} : decimalInteger s value →
      TokenRepresentation s (.APSInt value)

private def lineCharDecide (c : Char) :
    decides ((PLift (c = '\n') ⊕ PLift (c = '\r')) → Empty) :=
  if hn : c = '\n' then
    .inr (fun h => h (.inl ⟨hn⟩))
  else if hr : c = '\r' then
    .inr (fun h => h (.inr ⟨hr⟩))
  else
    .inl (fun h => match h with
      | .inl h => (hn h.down).elim
      | .inr h => (hr h.down).elim)


/-- The chosen lexeme cannot be extended to another token at this position. -/
private def MaximalToken (piece rest : String) : Type :=
  ∀ (suffix tail : String) (tok : Token),
    rest = suffix ++ tail → suffix ≠ "" →
    TokenRepresentation (piece ++ suffix) tok → Empty

/-- A word token must end before the next name character. -/
private def WordBoundary' (tok : Token) (rest : List Char) : Type :=
  match tok, rest with
  | .kw _, (c :: _)
  | .intType _, (c :: _)  => nameChar c → Empty
  | _, _ => Unit

-- nameChar
private def WordBoundary (tok : Token) (rest : String) : Type :=
  WordBoundary' tok rest.toList

/-- `piece` spells `tok` and is the longest lexeme at this position. -/
private def LongestMatch (piece : String) (tok : Token) (rest : String) : Type :=
  TokenRepresentation piece tok × MaximalToken piece rest × WordBoundary tok rest

/-- Splits source text into tokens, including whitespace and comments. -/
inductive Lexes : String → List (String × Token) → Type where
  | eof : Lexes "" [("", .Eof)]
  | token {piece rest : String} {tok : Token} {ts : List (String × Token)}
      : LongestMatch piece tok rest → tok ≠ .Eof →
      Lexes rest ts →
      Lexes (piece ++ rest) ((piece, tok) :: ts)


/-- Reasons the executable lexer can reject input. -/
inductive TokenizationError where
  | expectedNameAfter (sigil : Char)
  | unsupportedNumericLabel (name : String)
  | invalidInteger (spelling : String)
  | unsupportedWord (word : String)
  | unexpectedChar (c : Char)
  | noProgress
  deriving Repr, DecidableEq

/-- Classifies a maximal word, mirroring `WordToken`. -/
private def classifyWord (w : String) : Option Token :=
  match Keyword.all.find? (·.spelling == w), w.toList with
  | some k, _ => some (.kw k)
  | none, 'i' :: ds@(_ :: _) =>
      if ds.all Char.isDigit && (String.ofList ds).toNat! != 0 then
        some (.intType (String.ofList ds).toNat!)
      else none
  | none, _ => none

-- def hasSpan (p : A → Type) (l : List A) : Type :=
--   Σ (pre suf : List A), PLift (l = pre ++ suf) × All p pre
inductive HasSpan (p : A → Type) : List A → List A → List A →  Type where
  | nonempty (x : A) (pre suf : List A) : All p pre → (p x → Empty) → HasSpan p pre (x :: suf) (pre ++ x :: suf)
  | all (pre : List A) : All p pre → HasSpan p pre [] pre

/-- Compute a maximal prefix, retaining the witnesses for every accepted element. -/
def decideSpan {p : α → Type} (dp : (x : α) → decides (p x))
    (as : List α) : Σ (pre suf : List α), HasSpan p pre suf as :=
  loop as
where
  loop : (xs : List α) → Σ (pre suf : List α), HasSpan p pre suf xs
    | [] => ⟨[], [], .all [] .nil⟩
    | a :: xs =>
        match dp a with
        | .inr hn => ⟨[], a :: xs, .nonempty a [] xs .nil hn⟩
        | .inl ha =>
            match xs, loop xs with
            | _, ⟨_, _, .all pre hp⟩ =>
                ⟨a :: pre, [], .all (a :: pre) (.cons ha hp)⟩
            | _, ⟨_, _, .nonempty x pre suf hp hn⟩ =>
                ⟨a :: pre, x :: suf, .nonempty x (a :: pre) suf (.cons ha hp) hn⟩

/-- Scan one non-EOF token, returning its spelling, token, and remaining input.. -/
def scanOne : List Char → Except TokenizationError (List Char × Token × List Char)
  | [] => .error .noProgress
  | c :: cs => do
      let (tok, rest) ←
        match decideWS c with
        | .inl _ =>
            let ⟨_, rest, _⟩ := decideSpan decideWS cs
            .ok (.ws, rest)
        | .inr _ =>
            if c == ';' then
              let ⟨_, rest, _⟩ := decideSpan lineCharDecide cs
              .ok (.comment, rest.drop 1)
            else if c == '@' || c == '%' then
              match cs with
              | [] => .error (.expectedNameAfter c)
              | first :: _ =>
                  match nameStartDecide first with
                  | .inr _ => .error (.expectedNameAfter c)
                  | .inl _ =>
                      let ⟨name, rest, _⟩ := decideSpan nameCharDecide cs
                      let name := String.ofList name
                      .ok (if c == '@' then .GlobalVar name else .LocalVar name, rest)
            else
              match nameCharDecide c with
              | .inl _ =>
                  let ⟨word, after, _⟩ := decideSpan nameCharDecide (c :: cs)
                  let word := String.ofList word
                  if after.head? == some ':' && !word.all Char.isDigit then
                    .ok (.LabelStr word, after.drop 1)
                  else if c.isDigit || (c == '-' && cs.head?.any Char.isDigit) then
                    let (sign, body) := if c == '-' then ("-", cs) else ("", c :: cs)
                    let ⟨ds, rest, _⟩ := decideSpan
                      (fun c => toListDecide c "0123456789".toList) body
                    let spelling := sign ++ String.ofList ds
                    match spelling.toInt? with
                    | some n => .ok (.APSInt n, rest)
                    | none => .error (.invalidInteger spelling)
                  else
                    match classifyWord word with
                    | some tok => .ok (tok, after)
                    | none => .error (.unsupportedWord word)
              | .inr _ =>
                  match Punct.all.find? (·.char == c) with
                  | some p => .ok (.punct p, cs)
                  | none => .error (.unexpectedChar c)
      let piece := (c :: cs).take ((c :: cs).length - rest.length)
      return (piece, tok, rest)

/-- Scanning a specified maximal non-EOF lexeme returns exactly that lexeme,
its token, and the specified remainder. -/
theorem scanOne_success {piece rest : String} {tok : Token} :
    TokenRepresentation piece tok → tok ≠ .Eof →
    MaximalToken piece rest → WordBoundary tok rest →
    scanOne (piece ++ rest).toList = .ok (piece.toList, tok, rest.toList) := sorry

#reduce scanOne_success (piece := "12") (tok := .APSInt 12) (rest := ":")
#eval  scanOne ("12" ++ ":").toList

/-- The executable lexer for the token subset above. -/
private def tokenizerChars : List Char → Except TokenizationError (List (String × Token))
  | [] => .ok [("", .Eof)]
  | c :: cs => do
      let (piece, tok, rest) ← scanOne (c :: cs)
      -- Each recursive call is allowed only after consuming input.
      if _h : rest.length < (c :: cs).length then
        return (String.ofList piece, tok) :: (← tokenizerChars rest)
      else
        throw .noProgress
termination_by chars => chars.length

def tokenizer (s : String) : Except TokenizationError (List (String × Token)) :=
  tokenizerChars s.toList

/-- The De Morgan example used to exercise the LLVM token subset. -/
private def deMorganExample : String := "; De Morgan's laws, written without applying the simplification.
; In LLVM IR, xor with -1 flips every bit of an integer.

define i32 @demorgan_or(i32 %p, i32 %q) {
entry:
  %not_p = xor i32 %p, -1
  %not_q = xor i32 %q, -1
  %both_not = and i32 %not_p, %not_q
  %result = xor i32 %both_not, -1
  ret i32 %result
}

define i32 @demorgan_and(i32 %p, i32 %q) {
entry:
  %not_p = xor i32 %p, -1
  %not_q = xor i32 %q, -1
  %either_not = or i32 %not_p, %not_q
  %result = xor i32 %either_not, -1
  ret i32 %result
}
"


#eval (tokenizer deMorganExample)
#eval tokenizer "  \n\t%foo = -12; comment\n"
#eval tokenizer "  \n\t12:\n"

theorem tokenizer_success : Lexes s ts → tokenizer s = .ok ts := sorry

theorem tokenizer_fail : tokenizer s = .error message → Lexes s ts → False := by
  intro failed lexes
  rw [tokenizer_success lexes] at failed
  cases failed

def Parses : List (String × Token) → LLVMModule → Prop := sorry
/-- Every name is defined exactly once, numbering is consecutive, phis come first, ... -/
def WellFormed : LLVMModule → Prop := sorry
/-- Second pass: resolve forward references, turn phi nodes into block arguments. -/
def Elaborates : LLVMModule → VeIRModule → Prop := sorry

/-! ## Implementation -/

def parse : String → Option VeIRModule := sorry
def prettyPrint : VeIRModule → String := sorry

/-! ## Theorems -/

-- theorem grammar_parse (s : String) (v : VeIRModule) :
--     parse s = some v ↔
--       ∃ ts ast, Lexes s ts ∧ Parses ts ast ∧ WellFormed ast ∧ Elaborates ast v := sorry

/-- The grammar is unambiguous. -/
theorem parses_unambiguous (ts : List (String × Token)) (a₁ a₂ : LLVMModule) :
    Parses ts a₁ → Parses ts a₂ → a₁ = a₂ := sorry

/-- Syntactic equality of two VeIR programs up to renaming of values and blocks. -/
def EquivalentModuloNames : VeIRModule → VeIRModule → Prop := sorry

theorem parse_prettyPrint_round_trip (v : VeIRModule) :
    ∃ v', parse (prettyPrint v) = some v' ∧ EquivalentModuloNames v' v := sorry

end Veir.LLVMParser
