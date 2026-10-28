import Veir.GlobalOpInfo
import Veir.IR.WellFormed


/-!
# Proof-irrelevant proof sketch for Essay 1: a verified LLVM IR parser for VeIR

This copy keeps all correctness conditions in `Prop`, using builtin membership,
quantification, connectives, `Decidable`, and `Option`. Executable functions
return data; separate lemmas establish their correctness.
The parser and its main theorems are sketches; the token relation below has
explicit spelling rules.
The parser's output is a VeIR program: a well-formed `IRContext` over VeIR's
`OpCode` (which includes the LLVM dialect), together with the top-level
`builtin.module` operation.
-/

namespace Veir.LLVMParserProp

open Veir

/-! ## Tokens

Tokens needed for the two De Morgan functions in the example. Whitespace and
comments are represented explicitly in the lexical specification. -/

/-- Keywords are data: adding one means a constructor plus a spelling line. -/
inductive Keyword where
  | define | ret | xor | and | or
  deriving Repr, DecidableEq

def Keyword.all : List Keyword := [.define, .ret, .xor, .and, .or]

def Keyword.spelling : Keyword → List Char
  | .define => "define".toList | .ret => "ret".toList | .xor => "xor".toList | .and => "and".toList | .or => "or".toList

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

/-- Whitespace and comments are omitted from the parser-facing token stream. -/
def Token.isTrivia (t : Token) : Prop := t = .ws ∨ t = .comment

instance : DecidablePred Token.isTrivia := by
  intro t; unfold Token.isTrivia; infer_instance

/-- A VeIR program: a well-formed context plus its top-level module operation. -/
abbrev VeIRModule : Type := WfIRContext OpCode × OperationPtr

/-! ## Declarative specification -/

/-- ASCII character classes use Lean's builtin character predicates. -/
def asciiAlpha (c : Char) : Prop := c.isAlpha = true

def isDigit (c : Char) : Prop := c.isDigit = true

instance : DecidablePred asciiAlpha := fun c =>
  inferInstanceAs (Decidable (c.isAlpha = true))

instance : DecidablePred isDigit := fun c =>
  inferInstanceAs (Decidable (c.isDigit = true))

inductive digitNum : Char → Nat → Prop where
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


inductive digitsNum : List Char → Nat → Prop where
  | singleDigit : digitNum c n → digitsNum [c] n
  | digits : digitsNum cs n → digitNum d m → digitsNum (cs ++ [d]) (10 * n + m)



def nameStart (c : Char) : Prop :=
  asciiAlpha c ∨ c ∈ "-$._".toList

def nameChar (c : Char) : Prop :=
  nameStart c ∨ isDigit c

instance : DecidablePred nameStart := fun c =>
  inferInstanceAs (Decidable (asciiAlpha c ∨ c ∈ "-$._".toList))

instance : DecidablePred nameChar := fun c =>
  inferInstanceAs (Decidable (nameStart c ∨ isDigit c))

/-- Parse one decimal digit, returning only its value. -/
def decideDigit (c : Char) : Option Nat :=
  if c = '0' then some 0
  else if c = '1' then some 1
  else if c = '2' then some 2
  else if c = '3' then some 3
  else if c = '4' then some 4
  else if c = '5' then some 5
  else if c = '6' then some 6
  else if c = '7' then some 7
  else if c = '8' then some 8
  else if c = '9' then some 9
  else none

theorem digitNum.isDigit (h : digitNum c n) : isDigit c := by
  cases h <;> decide

theorem nameStart.nameChar (h : nameStart c) : nameChar c := Or.inl h

theorem isDigit.nameChar (h : isDigit c) : nameChar c := Or.inr h

theorem decideDigit_eq_some_iff : decideDigit c = some n ↔ digitNum c n := by
  grind (splits := 20) [decideDigit, digitNum]

/-- Append one decimal digit to an accumulated value. -/
def digitStep (n : Nat) (c : Char) : Option Nat :=
  (10 * n + ·) <$> decideDigit c

def decideDigits (s : List Char) : Option Nat :=
  if s = [] then none else s.foldlM digitStep 0

theorem digitsNum.ne_nil (h : digitsNum s n) : s ≠ [] := by
  cases h <;> simp

theorem digitsNum_snoc_iff : digitsNum (cs ++ [d]) n ↔
    (cs = [] ∧ digitNum d n) ∨ ∃ m k, digitsNum cs m ∧ digitNum d k ∧ n = 10 * m + k := by
  constructor
  · intro h; generalize he : cs ++ [d] = s at h
    cases h <;> simp_all [List.append_eq_singleton_iff] <;> grind
  · rintro (⟨rfl, h⟩ | ⟨m, k, hm, hk, rfl⟩) <;>
      solve_by_elim [digitsNum.singleDigit, digitsNum.digits]

theorem decideDigits_snoc : decideDigits (cs ++ [d]) =
    if cs = [] then decideDigit d else (decideDigits cs).bind (digitStep · d) := by
  by_cases cs = [] <;> simp_all [decideDigits, List.foldlM_append, digitStep]

theorem decideDigits_eq_some_iff : decideDigits s = some n ↔ digitsNum s n := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r.reverse := ⟨s.reverse, by simp⟩
  induction r generalizing n with
  | nil => simpa [decideDigits] using fun h => h.ne_nil rfl
  | cons d r ih =>
      rw [List.reverse_cons, decideDigits_snoc, digitsNum_snoc_iff]
      by_cases hr : r = [] <;>
        simp [hr, Option.bind_eq_some_iff, ih, digitStep, decideDigit_eq_some_iff] <;>
        grind [digitsNum.ne_nil]

def bareName (s : String) : Prop :=
  match s.toList with
  | [] => False
  | c :: cs => nameStart c ∧ ∀ c ∈ cs, nameChar c

def labelName (s : String) : Prop :=
  s ≠ "" ∧ ∀ c ∈ s.toList, nameChar c

def digits (s : String) : Prop :=
  s ≠ "" ∧ ∀ c ∈ s.toList, isDigit c

/-- A token's payload satisfies the lexical restrictions on its constructor. -/
def IsValidToken : Token → Prop
  | .LabelStr name => labelName name ∧ ¬digits name
  | .GlobalVar name | .LocalVar name => bareName name
  | _ => True

/-- Valid nontrivia tokens followed by exactly one final EOF token. -/
inductive IsValidTokenStream : List Token → Prop where
  | eof : IsValidTokenStream [.Eof]
  | cons : IsValidToken tok → ¬tok.isTrivia → tok ≠ .Eof →
      IsValidTokenStream ts → IsValidTokenStream (tok :: ts)

inductive decimalInteger : List Char → Int → Prop where
  | positive : digitsNum s n →  decimalInteger s n
  | negative  : digitsNum s n →  decimalInteger ('-' :: s) (-n)

theorem decimalInteger.nonempty (h : decimalInteger s n) : s ≠ [] := by
  cases h <;> grind [digitsNum.ne_nil]

def decideDecimal : List Char → Option Int
  | '-' :: cs => (decideDigits cs).map (fun (n : Nat) => -Int.ofNat n)
  | s => (decideDigits s).map Int.ofNat

theorem digitsNum.isDigits (h : digitsNum s n) : ∀ c ∈ s, isDigit c := by
  induction h with
  | singleDigit hd => simpa using hd.isDigit
  | digits _ hd ih => simpa [or_imp, forall_and] using ⟨ih, hd.isDigit⟩

theorem decideDecimal_eq_some_iff : decideDecimal s = some n ↔ decimalInteger s n := by
  have bad (ds : List Char) (m : Nat) (h : digitsNum ('-' :: ds) m) : False :=
    (by decide : ¬isDigit '-') (h.isDigits '-' (by simp))
  unfold decideDecimal
  split <;> simp only [Option.map_eq_some_iff, decideDigits_eq_some_iff]
  all_goals grind only [decimalInteger, → decimalInteger.positive, → decimalInteger.negative]

def noLinebreaks (s : List Char) : Prop :=
  ∀ c ∈ s, c ≠ '\n' ∧ c ≠ '\r'

/-- Tokens spelled by a maximal run of name characters: keywords and `iN` types. -/
inductive WordToken : List Char → Token → Prop where
  | keyword (k : Keyword) : WordToken k.spelling (.kw k)
  | intType {s : List Char} {n : Nat} : digitsNum s n → WordToken ('i' :: s) (.intType n)

def isWs (c : Char) : Prop := c ∈ " \t\n\r".toList

instance : DecidablePred isWs := fun c =>
  inferInstanceAs (Decidable (c ∈ " \t\n\r".toList))

/-- Spellings of the tokens in the example; boundaries belong to `Lexes`. -/
inductive TokenRepresentation : List Char → Token → Prop where
  | eof : TokenRepresentation [] .Eof
  | ws {s : List Char} : s ≠ [] →
      (∀ c ∈ s, isWs c) →
      TokenRepresentation s .ws
  | comment {line : List Char} {endChar : Char}
     :  noLinebreaks line → endChar ∈ "\n\r".toList →
      TokenRepresentation (';' :: (line ++ [endChar])) .comment
  | commentEof {line : List Char} :
      noLinebreaks line →
      TokenRepresentation (';' :: line) .comment
  | punct (p : Punct) : TokenRepresentation [p.char] (.punct p)
  | word {w : List Char} {tok : Token} : WordToken w tok → TokenRepresentation w tok
  | label (name : String) : labelName name ∧ ¬digits name →
      TokenRepresentation (name.toList ++ [':']) (.LabelStr name)
  | global (name : String) : bareName name →
      TokenRepresentation ('@' :: name.toList) (.GlobalVar name)
  | local (name : String) : bareName name →
      TokenRepresentation ('%' :: name.toList) (.LocalVar name)
  | integer {s : List Char} {value : Int} : decimalInteger s value →
      TokenRepresentation s (.APSInt value)
/-- Lexical units include unsupported words, so classification cannot split a word. -/
def LexemeRepresentation (piece : List Char) : Prop :=
  (∃ tok, TokenRepresentation piece tok) ∨
    (piece ≠ [] ∧ ∀ c ∈ piece, nameChar c)

/-- No longer lexical unit starts at this position, including unsupported words. -/
def MaximalLexeme (piece rest : List Char) : Prop :=
  ∀ n, 0 < n → n ≤ rest.length → ¬LexemeRepresentation (piece ++ rest.take n)

/-- Classify the entire maximal lexical unit as a supported token. -/
def LongestMatch (piece : List Char) (tok : Token) (rest : List Char) : Prop :=
  TokenRepresentation piece tok ∧ MaximalLexeme piece rest

/-- Splits source text into tokens, including whitespace and comments. -/
inductive Lexes : List Char → List (List Char × Token) → Prop where
  | eof : Lexes [] [([], .Eof)]
  | token {piece rest : List Char} {tok : Token} {ts : List (List Char × Token)}
      : LongestMatch piece tok rest → tok ≠ .Eof →
      Lexes rest ts →
      Lexes (piece ++ rest) ((piece, tok) :: ts)


/-- Reasons the executable lexer can reject input. -/
inductive TokenizationError where
  | expectedNameAfter (sigil : Char)
  | unsupportedWord (word : String)
  | unexpectedChar (c : Char)
  | noProgress
  deriving Repr, DecidableEq

/-- Classify a word, returning only its token. -/
def classifyWordRelevant (w : List Char) : Option Token :=
  match Keyword.all.find? (fun k => w == k.spelling) with
  | some k => some (.kw k)
  | none =>
      match w with
      | 'i' :: cs => (decideDigits cs).map Token.intType
      | _ => none

theorem classifyWordRelevant_eq_some_iff :
    classifyWordRelevant w = some tok ↔ WordToken w tok := by
  constructor
  · unfold classifyWordRelevant
    split <;> (try split) <;> (try simp only [Option.map_eq_some_iff])
    all_goals grind [WordToken.keyword, WordToken.intType, decideDigits_eq_some_iff]
  · intro h; cases h with
    | keyword k => cases k <;> decide
    | intType hd => simp [classifyWordRelevant, Keyword.all, Keyword.spelling,
        decideDigits_eq_some_iff.mpr hd]

/-- A complete comment body: any line break must be its final character. -/
def commentBody : List Char → Prop
  | [] => True
  | c :: cs => if c = '\n' ∨ c = '\r' then cs = [] else commentBody cs

instance instDecidableCommentBody : DecidablePred commentBody
  | [] => isTrue trivial
  | c :: cs =>
      letI := instDecidableCommentBody cs
      inferInstanceAs (Decidable (if c = '\n' ∨ c = '\r' then cs = [] else commentBody cs))

instance : DecidablePred bareName := fun s => by
  unfold bareName
  split <;> infer_instance

instance : DecidablePred labelName := fun s =>
  inferInstanceAs (Decidable (s ≠ "" ∧ ∀ c ∈ s.toList, nameChar c))

instance : DecidablePred digits := fun s =>
  inferInstanceAs (Decidable (s ≠ "" ∧ ∀ c ∈ s.toList, isDigit c))

/-- Recognize a whole lexeme. Choosing its length is the generic scanner's job. -/
def recognize : List Char → Option Token
  | [] => some .Eof
  | ';' :: cs => if commentBody cs then some .comment else none
  | '@' :: cs => if bareName (String.ofList cs) then some (.GlobalVar (String.ofList cs)) else none
  | '%' :: cs => if bareName (String.ofList cs) then some (.LocalVar (String.ofList cs)) else none
  | cs =>
      if ∀ c ∈ cs, isWs c then some .ws
      else if cs.getLast? = some ':' then
        let name := String.ofList cs.dropLast
        if labelName name ∧ ¬digits name then some (.LabelStr name) else none
      else match cs with
        | [c] => match Punct.all.find? (·.char == c) with
          | some p => some (.punct p)
          | none => (classifyWordRelevant cs).or ((decideDecimal cs).map Token.APSInt)
        | _ => (classifyWordRelevant cs).or ((decideDecimal cs).map Token.APSInt)

theorem commentBody_iff : commentBody cs ↔
    noLinebreaks cs ∨ ∃ line c, cs = line ++ [c] ∧ noLinebreaks line ∧ c ∈ "\n\r".toList := by
  induction cs with
  | nil => simp [commentBody, noLinebreaks]
  | cons c cs ih =>
      simp only [commentBody, List.cons_eq_append_iff, or_and_right, exists_or,
        noLinebreaks, List.mem_cons, forall_eq_or_imp] at *
      split <;> grind

theorem recognize_sound (h : recognize cs = some tok) : TokenRepresentation cs tok := by
  have last (xs : List Char) (h : xs.getLast? = some ':') : xs.dropLast ++ [':'] = xs := by
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h; simp
  unfold recognize at h; repeat' split at h
  all_goals simp_all [Option.or_eq_some_iff, Option.map_eq_some_iff,
    decideDecimal_eq_some_iff, classifyWordRelevant_eq_some_iff, commentBody_iff]
  all_goals grind only [intro TokenRepresentation, → TokenRepresentation.global,
    → TokenRepresentation.local, → TokenRepresentation.label, List.find?_some,
    = String.toList_ofList, = List.mem_cons, List.not_mem_nil]

/-- Name characters cannot start a comment, sigilled name, or whitespace token. -/
theorem nameChar_exclusions (hc : nameChar c) :
    c ≠ ';' ∧ c ≠ '@' ∧ c ≠ '%' ∧ ¬isWs c ∧ c ≠ ':' := by
  have : ∀ x ∈ [';', '@', '%', ' ', '\t', '\n', '\r', ':'], ¬nameChar x := by decide
  grind [isWs]

theorem recognize_name (hc : nameChar c) :
    recognize (c :: cs) =
      if (c :: cs).getLast? = some ':' then
        let name := String.ofList (c :: cs).dropLast
        if labelName name ∧ ¬digits name then some (.LabelStr name) else none
      else (classifyWordRelevant (c :: cs)).or ((decideDecimal (c :: cs)).map Token.APSInt) := by
  obtain ⟨hsemi, hat, hpercent, hws, _⟩ := nameChar_exclusions hc
  have hp : Punct.all.find? (·.char == c) = none := by
    have : ∀ x ∈ ['=', ',', '{', '}', '(', ')'], ¬nameChar x := by decide
    simp_all [Punct.all, Punct.char]; grind
  cases cs <;> simp [recognize, hsemi, hat, hpercent, hws, hp]

theorem recognize_ws (hne : cs ≠ []) (hw : ∀ c ∈ cs, isWs c) :
    recognize cs = some .ws := by
  cases cs <;> simp_all [recognize, isWs] <;> grind

theorem recognize_label (h : labelName name ∧ ¬digits name) :
    recognize (name.toList ++ [':']) = some (.LabelStr name) := by
  cases he : name.toList with
  | nil => simp_all [labelName]
  | cons c cs =>
      rw [List.cons_append, recognize_name (h.1.2 c (by simp [he]))]
      simp [← List.cons_append, ← he, h]

theorem recognize_word (h : WordToken cs tok) : recognize cs = some tok := by
  cases h with
  | keyword k => cases k <;> decide
  | @intType ds n hd =>
      rw [recognize_name (by decide)]
      have : ('i' :: ds).getLast? ≠ some ':' := by
        have := hd.isDigits; have : ¬isDigit ':' := by decide
        grind [List.mem_of_getLast?]
      simp [this, classifyWordRelevant_eq_some_iff.mpr (WordToken.intType hd)]

theorem decimalInteger.nameChars (h : decimalInteger cs n) : ∀ c ∈ cs, nameChar c := by
  cases h <;> grind [digitsNum.isDigits, isDigit.nameChar, show nameChar '-' by decide]

theorem decimalInteger.not_word (h : decimalInteger cs n) : ¬WordToken cs tok := by
  intro hw; cases hw with
  | keyword k =>
      have := decideDecimal_eq_some_iff.mpr h
      cases k <;> simp [Keyword.spelling, decideDecimal, decideDigits, digitStep, decideDigit] at this
  | intType _ => cases h with
      | positive h => exact (by decide : ¬isDigit 'i') (h.isDigits 'i' (by simp))

theorem recognize_integer (h : decimalInteger cs n) : recognize cs = some (.APSInt n) := by
  have hw : classifyWordRelevant cs = none := Option.eq_none_iff_forall_ne_some.mpr
    fun _ ht => h.not_word (classifyWordRelevant_eq_some_iff.mp ht)
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h.nonempty
  rw [recognize_name (h.nameChars c (by simp))]
  have : (c :: cs).getLast? ≠ some ':' := by
    have := h.nameChars; have : ¬nameChar ':' := by decide
    grind [List.mem_of_getLast?]
  simp [this, hw, decideDecimal_eq_some_iff.mpr h]

theorem recognize_complete (h : TokenRepresentation cs tok) : recognize cs = some tok := by
  cases h <;> try solve_by_elim [recognize_ws, recognize_label, recognize_word, recognize_integer]
  all_goals first
    | (rename_i p; cases p <;> decide)
    | (simp_all [recognize, commentBody_iff] <;> grind)

theorem recognize_eq_some_iff : recognize cs = some tok ↔ TokenRepresentation cs tok :=
  ⟨recognize_sound, recognize_complete⟩

theorem mem_reverse_range_prefix (h : (List.range k).reverse = l₁ ++ a :: l₂) :
    x ∈ l₁ ↔ a < x ∧ x < k := by
  rw [List.reverse_eq_append_iff, List.range_eq_range', List.range'_eq_append_iff] at h
  obtain ⟨_ | j, -, ha, hl⟩ := h
  · simp at ha
  · simp [List.range'_concat] at ha
    rw [← List.mem_reverse, hl, List.mem_range', ha.2]
    exact ⟨by omega, fun _ => ⟨x - (j + 1), by omega⟩⟩

/-- Try complete prefixes longest first. The recognizer is independent of the
search, which also works for other alphabets and token types. -/
def longestPrefix (decode : List α → Option β) (xs : List α) : Option (List α × β × List α) :=
  (List.range (xs.length + 1)).reverse.findSome? fun n =>
    (decode (xs.take n)).map (xs.take n, ·, xs.drop n)

theorem longestPrefix_eq_some_iff : longestPrefix decode xs = some (p, t, r) ↔
    xs = p ++ r ∧ decode p = some t ∧
    ∀ n, 0 < n → n ≤ r.length → decode (p ++ r.take n) = none := by
  simp only [longestPrefix, List.findSome?_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq]; constructor
  · rintro ⟨l₁, m, l₂, hl, ⟨t, ht, rfl, rfl, rfl⟩, hn⟩; refine ⟨by simp, ht, fun n _ _ => ?_⟩
    have := hn (m + n) ((mem_reverse_range_prefix hl).mpr (by grind)); simp_all [List.take_add]
  · rintro ⟨rfl, ht, hn⟩
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem (a := p.length)
      (l := (List.range ((p ++ r).length + 1)).reverse) (by simp; omega)
    refine ⟨l₁, p.length, l₂, hl, ⟨t, by simpa using ht, by simp, by simp, by simp⟩, ?_⟩
    intro x hx; have hx := (mem_reverse_range_prefix hl).mp hx
    simpa [List.take_append, List.take_of_length_le (by omega : p.length ≤ x)] using
      hn (x - p.length) (by omega) (by simp at hx; omega)

/-- Recognize lexical shape without requiring a supported token classification. -/
def recognizeLexeme (piece : List Char) : Option Unit :=
  if (recognize piece).isSome ∨ (piece ≠ [] ∧ ∀ c ∈ piece, nameChar c)
  then some () else none

theorem recognizeLexeme_eq_some_iff :
    recognizeLexeme piece = some () ↔ LexemeRepresentation piece := by
  simp [recognizeLexeme, LexemeRepresentation, Option.isSome_iff_exists,
    recognize_eq_some_iff]
  grind

theorem recognizeLexeme_eq_none_iff :
    recognizeLexeme piece = none ↔ ¬LexemeRepresentation piece := by
  rw [← recognizeLexeme_eq_some_iff]
  cases recognizeLexeme piece with
  | none => simp
  | some u => cases u; simp

/-- Length selection is independent of classification of the selected unit. -/
theorem longestPrefix_lexeme :
    longestPrefix recognizeLexeme input = some (piece, (), rest) ↔
    input = piece ++ rest ∧ LexemeRepresentation piece ∧ MaximalLexeme piece rest := by
  simp [longestPrefix_eq_some_iff, recognizeLexeme_eq_some_iff, MaximalLexeme,
    recognizeLexeme_eq_none_iff]

structure ScanResult where
  piece : List Char
  tok : Token
  rest : List Char
  deriving Repr, DecidableEq

def ScanResult.toTuple (result : ScanResult) : List Char × Token × List Char :=
  (result.piece, result.tok, result.rest)

/-- Preserve the dispatcher's diagnostics when no valid token can be consumed. -/
def rejection : List Char → TokenizationError
  | [] => .noProgress
  | c :: cs =>
      if c = '@' ∨ c = '%' then .expectedNameAfter c
      else if nameChar c then
        .unsupportedWord (String.ofList ((c :: cs).takeWhile (fun c => decide (nameChar c))))
      else .unexpectedChar c

/-- Select a whole lexical unit, then classify it. EOF is emitted by `tokenizerChars`. -/
def scanOne (input : List Char) : Except TokenizationError ScanResult :=
  match longestPrefix recognizeLexeme input with
  | some (piece, (), rest) =>
      match recognize piece with
      | some tok => if piece ≠ [] then .ok ⟨piece, tok, rest⟩ else .error (rejection input)
      | none => .error (rejection input)
  | none => .error (rejection input)

-- Unsupported words remain whole; a longer supported label is still selected.
#guard (scanOne "i32 ".toList).map ScanResult.toTuple ==
  .ok ("i32".toList, .intType 32, [' '])
#guard (scanOne "i32foo ".toList).map ScanResult.toTuple ==
  .error (.unsupportedWord "i32foo")
#guard (scanOne "addendum".toList).map ScanResult.toTuple ==
  .error (.unsupportedWord "addendum")
#guard (scanOne "123abc".toList).map ScanResult.toTuple ==
  .error (.unsupportedWord "123abc")
#guard (scanOne "i32foo:".toList).map ScanResult.toTuple ==
  .ok ("i32foo:".toList, .LabelStr "i32foo", [])

theorem scanOne_eq_ok_iff : scanOne input = .ok result ↔
    input = result.piece ++ result.rest ∧ result.piece ≠ [] ∧
    LongestMatch result.piece result.tok result.rest := by
  rcases result with ⟨piece, tok, rest⟩
  refine ⟨fun h => ?_, fun ⟨hs, hne, ht, hm⟩ => ?_⟩
  · unfold scanOne at h
    split at h <;> (try split at h) <;> (try split at h) <;> cases h
    simp_all [longestPrefix_lexeme, recognize_eq_some_iff, LongestMatch]
  · simp [scanOne, longestPrefix_lexeme.mpr ⟨hs, .inl ⟨tok, ht⟩, hm⟩,
      recognize_eq_some_iff.mpr ht, hne]

theorem scanOne_progress (h : scanOne input = .ok result) :
    result.rest.length < input.length := by
  obtain ⟨rfl, hn, -⟩ := scanOne_eq_ok_iff.mp h
  simpa using List.length_pos_iff.mpr hn

/-- Only the empty lexeme spells EOF. -/
theorem TokenRepresentation.ne_nil_iff (h : TokenRepresentation piece tok) :
    piece ≠ [] ↔ tok ≠ .Eof := by
  refine ⟨fun hp ht => ?_, fun ht hp => ?_⟩
  · subst ht; cases h with | eof => exact hp rfl | word hw => cases hw
  · subst hp; simp [← recognize_eq_some_iff, recognize] at h; exact ht h.symm

theorem scanOne_success_result (hr : TokenRepresentation piece tok) (hne : tok ≠ .Eof)
    (hm : MaximalLexeme piece rest) :
    scanOne (piece ++ rest) = .ok ⟨piece, tok, rest⟩ :=
  scanOne_eq_ok_iff.mpr ⟨rfl, hr.ne_nil_iff.mpr hne, hr, hm⟩

/-- Scanning a specified maximal non-EOF lexeme returns that exact lexeme. -/
theorem scanOne_success {piece rest : List Char} {tok : Token} :
    TokenRepresentation piece tok → tok ≠ .Eof →
    MaximalLexeme piece rest →
    (scanOne (piece ++ rest)).map ScanResult.toTuple = .ok (piece, tok, rest) := by
  intro hr hne hm; rw [scanOne_success_result hr hne hm]; rfl

/-- The executable lexer for the token subset above. -/
def tokenizerChars : List Char → Except TokenizationError (List (List Char × Token))
  | [] => .ok [([], .Eof)]
  | c :: cs => do
      match _h : scanOne (c :: cs) with
      | .error err => .error err
      | .ok result => do
          return (result.piece, result.tok) :: (← tokenizerChars result.rest)
termination_by chars => chars.length
decreasing_by exact scanOne_progress _h

def tokenizer (s : String) : Except TokenizationError (List (List Char × Token)) :=
  tokenizerChars s.toList

/-- The parser-facing tokens of a lexeme list. -/
def significant (ts : List (List Char × Token)) : List Token :=
  (ts.map Prod.snd).filter (fun tok => decide (¬tok.isTrivia))

/-- Tokenize while discarding original spellings, whitespace, and comments. -/
def tokenizer' (s : String) : Except TokenizationError (List Token) :=
  (tokenizer s).map significant

/-- The De Morgan example used to exercise the LLVM token subset. -/
def deMorganExample : String := "; De Morgan's laws, written without applying the simplification.
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


theorem tokenizerChars_complete (h : Lexes input ts) : tokenizerChars input = .ok ts := by
  induction h with
  | eof => simp [tokenizerChars]
  | @token piece rest tok ts hm hne hl ih =>
      have hs := scanOne_success_result hm.1 hne hm.2
      have hp := hm.1.ne_nil_iff.mpr hne
      cases piece <;> simp_all [tokenizerChars]
      split <;> simp_all <;> rfl

theorem tokenizerChars_sound (h : tokenizerChars input = .ok ts) : Lexes input ts := by
  fun_induction tokenizerChars input generalizing ts with
  | case1 => cases h; exact .eof
  | case2 => cases h
  | case3 c cs result hs ih =>
      obtain ⟨he, hn, hm⟩ := scanOne_eq_ok_iff.mp hs
      cases hr : tokenizerChars result.rest <;> simp only [hr] at h <;> cases h
      exact he ▸ .token hm (hm.1.ne_nil_iff.mp hn) (ih hr)

theorem tokenizer_eq_ok_iff : tokenizer s = .ok ts ↔ Lexes s.toList ts :=
  ⟨tokenizerChars_sound, tokenizerChars_complete⟩

theorem tokenizer_success : Lexes s.toList ts → tokenizer s = .ok ts :=
  tokenizerChars_complete

/-- The token-only tokenizer inherits completeness from `tokenizer`. -/
theorem tokenizer'_success (h : Lexes s.toList ts) :
    tokenizer' s = .ok (significant ts) := by
  rw [tokenizer', tokenizer_success h]
  rfl

theorem tokenizer_fail : tokenizer s = .error message → Lexes s.toList ts → False := by
  intro failed lexes; simp [tokenizer_success lexes] at failed

/-- A simple spelling for each token. -/
def Token.spelling : Token → String
    | .Eof => ""
    | .ws => " "
    | .comment => ";\n"
    | .punct p => String.ofList [p.char]
    | .kw k => String.ofList k.spelling
    | .intType width => "i" ++ toString width
    | .LabelStr name => name ++ ":"
    | .GlobalVar name => "@" ++ name
    | .LocalVar name => "%" ++ name
    | .APSInt value => toString value

/-- Print each significant token followed by a space; EOF is implicit. -/
def printTokens (ts : List Token) : String :=
  ts.foldr (fun t s => if t = .Eof then s else t.spelling ++ " " ++ s) ""

/--
info: Except.ok "define i32 @demorgan_or ( i32 %p , i32 %q ) { entry: %not_p = xor i32 %p , -1 %not_q = xor i32 %q , -1 %both_not = and i32 %not_p , %not_q %result = xor i32 %both_not , -1 ret i32 %result } define i32 @demorgan_and ( i32 %p , i32 %q ) { entry: %not_p = xor i32 %p , -1 %not_q = xor i32 %q , -1 %either_not = or i32 %not_p , %not_q %result = xor i32 %either_not , -1 ret i32 %result } "
-/
#guard_msgs in #eval (printTokens <$> tokenizer' deMorganExample)

theorem digitsNum_toDigits (n : Nat) : digitsNum (Nat.toDigits 10 n) n := by
  have small : ∀ n : Fin 10, decideDigit n.val.digitChar = some n.val := by decide
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [Nat.toDigits_eq_ite (by decide)]
      split
      · exact .singleDigit (decideDigit_eq_some_iff.mp (small ⟨n, by assumption⟩))
      · simpa [Nat.div_add_mod] using digitsNum.digits (ih (n / 10) (by omega))
          (decideDigit_eq_some_iff.mp (small ⟨n % 10, by omega⟩))

theorem decimalInteger_toString (n : Int) : decimalInteger (toString n).toList n := by
  cases n with
  | ofNat n => simpa [Int.repr] using decimalInteger.positive (digitsNum_toDigits n)
  | negSucc n =>
      change decimalInteger ("-" ++ Nat.repr (n + 1)).toList (Int.negSucc n)
      simpa [Int.negSucc_eq] using decimalInteger.negative (digitsNum_toDigits (n + 1))

theorem TokenRepresentation.spelling (h : TokenRepresentation piece tok) :
    TokenRepresentation tok.spelling.toList tok := by
  cases h with
  | eof => exact .eof
  | ws _ _ => exact .ws (by decide) (by decide)
  | comment _ _ | commentEof _ =>
      exact .comment (line := []) (endChar := '\n') (by simp [noLinebreaks]) (by decide)
  | punct p => simpa [Token.spelling] using TokenRepresentation.punct p
  | word hw => cases hw with
    | keyword k => simpa [Token.spelling] using TokenRepresentation.word (WordToken.keyword k)
    | intType _ => simpa [Token.spelling] using
        TokenRepresentation.word (WordToken.intType (digitsNum_toDigits _))
  | label name h => simpa [Token.spelling] using TokenRepresentation.label name h
  | global name h => simpa [Token.spelling] using TokenRepresentation.global name h
  | «local» name h => simpa [Token.spelling] using TokenRepresentation.local name h
  | integer _ => exact .integer (decimalInteger_toString _)


theorem TokenRepresentation.spelling2 (h : IsValidToken tok) :
    TokenRepresentation tok.spelling.toList tok := by
  cases tok <;> simp only [IsValidToken] at h
  all_goals apply TokenRepresentation.spelling
  case ws => exact .ws (s := [' ']) (by decide) (by decide)
  case comment => exact .commentEof (line := []) (by simp [noLinebreaks])
  all_goals solve_by_elim [TokenRepresentation.eof, TokenRepresentation.punct,
    TokenRepresentation.word, WordToken.keyword, WordToken.intType, digitsNum_toDigits,
    TokenRepresentation.label, TokenRepresentation.global, TokenRepresentation.local,
    TokenRepresentation.integer, decimalInteger_toString]

theorem nameChar.not_ws_or_semicolon (h : nameChar c) : ¬isWs c ∧ c ≠ ';' :=
  ⟨(nameChar_exclusions h).2.2.2.1, (nameChar_exclusions h).1⟩


theorem bareName.nameChars (h : bareName name) : ∀ c ∈ name.toList, nameChar c := by
  unfold bareName at h
  split at h <;> simp_all [nameStart.nameChar]

theorem WordToken.nameChars (h : WordToken piece tok) : ∀ c ∈ piece, nameChar c := by
  cases h with
  | keyword k => cases k <;> decide
  | intType hd => grind [digitsNum.isDigits, isDigit.nameChar, show nameChar 'i' by decide]

/-- Significant lexemes contain neither whitespace nor a comment opener. -/
theorem TokenRepresentation.significant_chars (h : TokenRepresentation piece tok)
    (ht : ¬tok.isTrivia) : ∀ c ∈ piece, ¬isWs c ∧ c ≠ ';' := by
  cases h with
  | eof | ws _ _ | comment _ _ | commentEof _ => simp_all [Token.isTrivia]
  | punct p => cases p <;> decide
  | word hw => exact fun c hc => (hw.nameChars c hc).not_ws_or_semicolon
  | label name hn =>
      exact List.forall_mem_append.mpr
        ⟨fun c hc => (hn.1.2 c hc).not_ws_or_semicolon, by decide⟩
  | global name hn | «local» name hn =>
      exact List.forall_mem_cons.mpr ⟨by decide, fun c hc => (hn.nameChars c hc).not_ws_or_semicolon⟩
  | integer hd => exact fun c hc => (hd.nameChars c hc).not_ws_or_semicolon

theorem TokenRepresentation.trivia (h : TokenRepresentation piece tok)
    (ht : tok.isTrivia) :
    (∀ c ∈ piece, isWs c) ∨ ∃ cs, piece = ';' :: cs := by
  cases h <;> simp_all [Token.isTrivia]
  cases ‹WordToken _ _› <;> simp_all

theorem TokenRepresentation.maximal_space (h : TokenRepresentation piece tok)
    (ht : ¬tok.isTrivia) (hne : tok ≠ .Eof) :
    MaximalLexeme piece (' ' :: rest) := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil (h.ne_nil_iff.mpr hne)
  intro n hn _ hr
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rcases hr with ⟨tok, hr⟩ | ⟨_, hw⟩
  · have hs := fun ht' => (hr.significant_chars ht' ' ' (by simp)).1 (by decide)
    rcases hr.trivia (Classical.byContradiction hs) with hw | ⟨_, he⟩
    · exact (h.significant_chars ht c (by simp)).1 (hw c (by simp))
    · exact (h.significant_chars ht c (by simp)).2 (List.cons_eq_cons.mp he).1
  · exact (by decide : ¬nameChar ' ') (hw ' ' (by simp))

theorem TokenRepresentation.first_not_ws (h : TokenRepresentation piece tok)
    (ht : ¬tok.isTrivia) (hne : tok ≠ .Eof) :
    ∀ c cs, piece ++ rest = c :: cs → ¬isWs c := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil (h.ne_nil_iff.mpr hne)
  simpa using (h.significant_chars ht c (by simp)).1

/-- No lexeme starts with a space followed by a non-whitespace character. -/
theorem recognize_space_cons (hc : ¬isWs c) : recognize (' ' :: c :: cs) = none := by
  simp [recognize, hc, labelName, nameChar, nameStart, asciiAlpha, isDigit, classifyWordRelevant,
    Keyword.all, Keyword.spelling, decideDecimal, decideDigits, digitStep, decideDigit]

theorem Lexes.space (h : Lexes input ts) (hc : ∀ c cs, input = c :: cs → ¬isWs c) :
    Lexes (' ' :: input) (([' '], .ws) :: ts) := by
  refine .token ⟨.ws (s := [' ']) (by simp) (by decide), fun n hn hl hr => ?_⟩ (by decide) h
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil (l := input) (by rintro rfl; simp at hl; omega)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rcases hr with ⟨tok, hr⟩ | ⟨_, hw⟩
  · simpa [recognize_space_cons (hc c cs rfl)] using recognize_eq_some_iff.mpr hr
  · exact (by decide : ¬nameChar ' ') (hw ' ' (by simp))

theorem printTokens_cons (hne : tok ≠ .Eof) :
    (printTokens (tok :: ts)).toList = tok.spelling.toList ++ ' ' :: (printTokens ts).toList := by
  simp [printTokens, hne, String.toList_append]

theorem significant_cons : significant ((p, tok) :: ts) =
    if tok.isTrivia then significant ts else tok :: significant ts := by
  by_cases tok.isTrivia <;> simp [significant, *]

/-- Reprint significant lexemes, each followed by a whitespace lexeme. -/
theorem Lexes.reprint (h : Lexes input ts) :
    ∃ printed, Lexes (printTokens (significant ts)).toList printed ∧
      significant printed = significant ts ∧
      ∀ c cs, (printTokens (significant ts)).toList = c :: cs → ¬isWs c := by
  induction h with
  | eof => exact ⟨_, .eof, rfl, by simp [printTokens, significant, Token.isTrivia]⟩
  | @token piece rest tok ts hm hne hl ih =>
      obtain ⟨printed, hp, he, hc⟩ := ih
      rw [significant_cons]; split
      · exact ⟨printed, hp, he, hc⟩
      rw [printTokens_cons hne]
      refine ⟨_, .token ⟨hm.1.spelling, hm.1.spelling.maximal_space ‹_› hne⟩
        hne (hp.space hc), ?_, hm.1.spelling.first_not_ws ‹_› hne⟩
      simp [significant_cons, *, show Token.ws.isTrivia from .inl rfl]

/-- Printing a valid token stream gives lexemes with the same significant tokens. -/
theorem IsValidTokenStream.print_lexes (h : IsValidTokenStream ts) :
    ∃ printed, Lexes (printTokens ts).toList printed ∧ significant printed = ts ∧
      ∀ c cs, (printTokens ts).toList = c :: cs → ¬isWs c := by
  induction h with
  | eof => exact ⟨_, .eof, rfl, by simp [printTokens]⟩
  | @cons tok ts hv ht hne _ ih =>
      obtain ⟨printed, hp, he, hc⟩ := ih
      have hr := TokenRepresentation.spelling2 hv
      rw [printTokens_cons hne]
      refine ⟨_, .token ⟨hr, hr.maximal_space ht hne⟩
        hne (hp.space hc), ?_, hr.first_not_ws ht hne⟩
      simp [significant_cons, ht, he, show Token.ws.isTrivia from .inl rfl]

/-- Printing and retokenizing preserves any valid token stream. -/
theorem tokenizer'_printTokens_round_trip (h : IsValidTokenStream ts) :
    tokenizer' (printTokens ts) = .ok ts := by
  obtain ⟨printed, hp, he, -⟩ := h.print_lexes
  rw [tokenizer', tokenizer_success hp, ← he]; rfl


end Veir.LLVMParserProp
