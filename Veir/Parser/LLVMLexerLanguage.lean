import Veir.Parser.LexerLanguage

/-!
# The Essay 1 LLVM lexer as data

This mirrors the token subset and rejection behavior of `Veir.Parser.LLVMLexer`.
It is standalone: importing it does not import that sketch or its placeholders.
The token types have the same constructors, in a separate namespace.

`rules` contains the spelling grammars, decoding actions, and boundary checks.
`TokenRepresentation`, `LongestMatch`, and `Lexes` give independent `Prop`
semantics; `scanOne` and `tokenizer` interpret the same rules executably.
Agreement with these relations and with the original lexer remains to be proved.
-/

namespace Veir.LexerLanguage.LLVM

inductive Keyword where
  | define | ret | xor | and | or
  deriving Repr, DecidableEq

def Keyword.spelling : Keyword → String
  | .define => "define" | .ret => "ret" | .xor => "xor" | .and => "and" | .or => "or"

inductive Punct where
  | equal | comma | lbrace | rbrace | lparen | rparen
  deriving Repr, DecidableEq

def Punct.spelling : Punct → String
  | .equal => "=" | .comma => "," | .lbrace => "{" | .rbrace => "}"
  | .lparen => "(" | .rparen => ")"

inductive Token where
  | Eof | ws | comment
  | punct (p : Punct)
  | kw (k : Keyword)
  | intType (width : Nat)
  | LabelStr (name : String)
  | GlobalVar (name : String)
  | LocalVar (name : String)
  | APSInt (value : Int)
  deriving Repr, DecidableEq

inductive TokenizationError where
  | expectedNameAfter (sigil : Char)
  | unsupportedNumericLabel (name : String)
  | invalidInteger (spelling : String)
  | unsupportedWord (word : String)
  | unexpectedChar (c : Char)
  | noProgress
  deriving Repr, DecidableEq

def digitClass : CharClass := .range '0' '9'
def nameStartClass : CharClass := Examples.nameStart
def nameCharClass : CharClass := Examples.nameChar
def whitespaceClass : CharClass := .oneOf " \t\n\r".toList
def newlineClass : CharClass := .oneOf "\n\r".toList
def digit : Lexer := .charClass digitClass
def bareName : Lexer := Examples.bareName
def nameRun : Lexer := (Lexer.charClass nameCharClass).plus

/-- A label name contains at least one nondigit. This excludes numeric labels
without excluding names that begin with digits, such as `12foo:`. -/
def labelName : Lexer :=
  .seq (.star digit) (.seq (.charClass nameStartClass) (.star (.charClass nameCharClass)))

inductive Boundary where
  | any
  | notFollowedBy (cls : CharClass)
  | eof
  deriving Repr, DecidableEq

def Boundary.denote : Boundary → List Char → Prop
  | .any, _ => True
  | .notFollowedBy _, [] => True
  | .notFollowedBy cls, c :: _ => ¬cls.denote c
  | .eof, rest => rest = []

def Boundary.accepts : Boundary → List Char → Bool
  | .any, _ => true
  | .notFollowedBy _, [] => true
  | .notFollowedBy cls, c :: _ => !(cls.denote c)
  | .eof, rest => rest.isEmpty

/-- Decoding actions are data too; their inputs are complete matched lexemes. -/
inductive Action where
  | fixed (token : Token)
  | intType | label | global | local | integer
  deriving Repr, DecidableEq

def Action.decode : Action → List Char → Option Token
  | .fixed token, _ => some token
  | .intType, chars => (String.ofList (chars.drop 1)).toNat?.map Token.intType
  | .label, chars => some (.LabelStr (String.ofList (chars.take (chars.length - 1))))
  | .global, chars => some (.GlobalVar (String.ofList (chars.drop 1)))
  | .local, chars => some (.LocalVar (String.ofList (chars.drop 1)))
  | .integer, '-' :: chars =>
      (String.ofList chars).toNat?.map (fun n => .APSInt (-Int.ofNat n))
  | .integer, chars => (String.ofList chars).toNat?.map (fun n => .APSInt (Int.ofNat n))

structure Rule where
  lexer : Lexer
  action : Action
  boundary : Boundary := .any
  deriving Repr, DecidableEq

def rules : List Rule :=
  [ ⟨(Lexer.charClass whitespaceClass).plus, .fixed .ws, .any⟩,
    ⟨.seq (.literal ";")
        (.seq (.star (.charClass (.complement newlineClass))) (.charClass newlineClass)),
      .fixed .comment, .any⟩,
    ⟨.seq (.literal ";") (.star (.charClass (.complement newlineClass))),
      .fixed .comment, .eof⟩,
    ⟨.seq (.literal "i") digit.plus, .intType, .notFollowedBy nameCharClass⟩,
    ⟨.seq labelName (.literal ":"), .label, .any⟩,
    ⟨.seq (.literal "@") bareName, .global, .any⟩,
    ⟨.seq (.literal "%") bareName, .local, .any⟩,
    ⟨.alt digit.plus (.seq (.literal "-") digit.plus), .integer, .any⟩ ] ++
  ([Keyword.define, .ret, .xor, .and, .or].map (fun k =>
    ⟨.literal k.spelling, .fixed (.kw k), .notFollowedBy nameCharClass⟩)) ++
  ([Punct.equal, .comma, .lbrace, .rbrace, .lparen, .rparen].map (fun p =>
    ⟨.literal p.spelling, .fixed (.punct p), .any⟩))

/-- EOF is represented separately and is never a consuming token rule. -/
def TokenRepresentation (piece : List Char) (tok : Token) : Prop :=
  (piece = [] ∧ tok = .Eof) ∨
  ∃ rule ∈ rules, Matches rule.lexer piece ∧ rule.action.decode piece = some tok

def MaximalToken (piece rest : List Char) : Prop :=
  ∀ suffix tail tok, rest = suffix ++ tail → suffix ≠ [] →
    ¬TokenRepresentation (piece ++ suffix) tok

def LongestMatch (piece : List Char) (tok : Token) (rest : List Char) : Prop :=
  (∃ rule ∈ rules, Matches rule.lexer piece ∧ rule.action.decode piece = some tok ∧
    rule.boundary.denote rest) ∧ MaximalToken piece rest

inductive Lexes : List Char → List (List Char × Token) → Prop where
  | eof : Lexes [] [([], .Eof)]
  | token : LongestMatch piece tok rest → tok ≠ .Eof → Lexes rest tokens →
      Lexes (piece ++ rest) ((piece, tok) :: tokens)

structure ScanResult where
  piece : List Char
  tok : Token
  rest : List Char
  deriving Repr, DecidableEq

/-- Select maximal spelling length before checking boundaries. Thus `definefoo`
cannot fall back to the shorter keyword `define`. -/
def candidate (input : List Char) : Option ScanResult :=
  let lengths := (List.range input.length).reverse.map (· + 1)
  let longest := lengths.find? (fun n =>
    rules.any (fun rule => rule.lexer.matches (input.take n)))
  longest.bind (fun n =>
    let piece := input.take n
    let rest := input.drop n
    rules.findSome? (fun rule =>
      if rule.lexer.matches piece && rule.boundary.accepts rest then
        (rule.action.decode piece).map (fun tok => ⟨piece, tok, rest⟩)
      else none))

/-- Mirror the original dispatcher's diagnostics when no rule can consume input.
The original's numeric-label and invalid-integer error constructors are retained,
although its current dispatcher does not produce them. -/
def rejection : List Char → TokenizationError
  | [] => .noProgress
  | c :: cs =>
      if c = '@' ∨ c = '%' then .expectedNameAfter c
      else if nameCharClass.denote c then
        .unsupportedWord (String.ofList ((c :: cs).takeWhile
          (fun ch => decide (nameCharClass.denote ch))))
      else .unexpectedChar c

def scanOne (input : List Char) : Except TokenizationError ScanResult :=
  match candidate input with
  | some result => .ok result
  | none => .error (rejection input)

/-- Each successful scan consumes at least one character. A fuel bound keeps
the interpreter total without needing a termination proof about `candidate`. -/
def tokenizerFuel : Nat → List Char → Except TokenizationError (List (List Char × Token))
  | _, [] => .ok [([], .Eof)]
  | 0, _ :: _ => .error .noProgress
  | fuel + 1, input@(_ :: _) => do
      let result ← scanOne input
      let tokens ← tokenizerFuel fuel result.rest
      return (result.piece, result.tok) :: tokens

def tokenizer (text : String) : Except TokenizationError (List (List Char × Token)) :=
  tokenizerFuel text.toList.length text.toList

end Veir.LexerLanguage.LLVM
