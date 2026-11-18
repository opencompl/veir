import Std

/-!
# A declarative language for lexers

`Lexer` is syntax, `Lexer.language` is its meaning in `Prop`, and
`Lexer.matches` interprets it as an executable recognizer. Recognition consumes
the entire input; `Lexer.longestPrefix` adds maximal-prefix scanning.

The interpreter favors simplicity over speed. Sequencing tries every split.
Repetition uses a table of accepted prefix lengths, so it terminates even when
its body accepts the empty string, without enumerating all partitions.
The declarative semantics is independent of the interpreter; their equivalence
is not yet proved here.
-/

namespace Veir.LexerLanguage

/-- Character classes are data, including Boolean combinations of classes. -/
inductive CharClass where
  | any
  | oneOf (chars : List Char)
  | range (first last : Char)
  | union (left right : CharClass)
  | intersection (left right : CharClass)
  | complement (body : CharClass)
  deriving Repr, DecidableEq

def CharClass.denote : CharClass → Char → Prop
  | .any, _ => True
  | .oneOf chars, c => c ∈ chars
  | .range first last, c => first.toNat ≤ c.toNat ∧ c.toNat ≤ last.toNat
  | .union left right, c => left.denote c ∨ right.denote c
  | .intersection left right, c => left.denote c ∧ right.denote c
  | .complement body, c => ¬body.denote c

instance CharClass.decidableDenote (cls : CharClass) : DecidablePred (cls.denote) := fun c =>
  match cls with
  | .any => inferInstanceAs (Decidable True)
  | .oneOf chars => inferInstanceAs (Decidable (c ∈ chars))
  | .range first last => inferInstanceAs
      (Decidable (first.toNat ≤ c.toNat ∧ c.toNat ≤ last.toNat))
  | .union left right =>
      letI := left.decidableDenote c
      letI := right.decidableDenote c
      inferInstanceAs (Decidable (left.denote c ∨ right.denote c))
  | .intersection left right =>
      letI := left.decidableDenote c
      letI := right.decidableDenote c
      inferInstanceAs (Decidable (left.denote c ∧ right.denote c))
  | .complement body =>
      letI := body.decidableDenote c
      inferInstanceAs (Decidable (¬body.denote c))

/-- A regular language. `literal ""` accepts the empty string; `empty` accepts nothing. -/
inductive Lexer where
  | empty
  | literal (text : String)
  | charClass (cls : CharClass)
  | seq (left right : Lexer)
  | alt (left right : Lexer)
  | star (body : Lexer)
  deriving Repr, DecidableEq

def Lexer.plus (body : Lexer) : Lexer := .seq body (.star body)

def Lexer.optional (body : Lexer) : Lexer := .alt (.literal "") body

/-- Declarative matching, with no reference to the executable recognizer. -/
inductive Matches : Lexer → List Char → Prop where
  | literal (text : String) : Matches (.literal text) text.toList
  | charClass (h : cls.denote c) : Matches (.charClass cls) [c]
  | seq : Matches left xs → Matches right ys → Matches (.seq left right) (xs ++ ys)
  | altLeft : Matches left xs → Matches (.alt left right) xs
  | altRight : Matches right xs → Matches (.alt left right) xs
  | starNil : Matches (.star body) []
  | starCons : Matches body xs → Matches (.star body) ys → Matches (.star body) (xs ++ ys)

/-- Interpret a lexer as a predicate on source strings. -/
def Lexer.language (lexer : Lexer) (text : String) : Prop :=
  Matches lexer text.toList

/-- The table entry at `i` says whether the first `i` characters match `body*`.
Only nonempty final pieces are considered: empty repetitions can be omitted.
There are quadratically many candidate pieces, each passed to `accept` once.
-/
def repeatMatches (accept : List Char → Bool) (input : List Char) : Bool :=
  let table := (List.range input.length).foldl (fun (table : Array Bool) k =>
    let stop := k + 1
    let accepted := (List.range stop).any (fun start =>
      table[start]! && accept ((input.drop start).take (stop - start)))
    table.push accepted) #[true]
  table[input.length]!

/-- An executable interpretation, structurally recursive on lexer syntax.
Alternatives denote union, rather than committing to the first successful branch.
The total runtime depends on nested rules and the cost of recognizing each piece;
the quadratic candidate count for repetition is not a global runtime bound.
-/
def Lexer.matches : Lexer → List Char → Bool
  | .empty, _ => false
  | .literal text, input => input == text.toList
  | .charClass cls, input =>
      match input with
      | [c] => decide (cls.denote c)
      | _ => false
  | .seq (.literal text) right, input =>
      let leading := text.toList
      input.take leading.length == leading && right.matches (input.drop leading.length)
  | .seq (.charClass cls) right, input =>
      match input with
      | [] => false
      | c :: rest => decide (cls.denote c) && right.matches rest
  | .seq left (.literal text), input =>
      let suffix := text.toList
      suffix.length ≤ input.length &&
        input.drop (input.length - suffix.length) == suffix &&
        left.matches (input.take (input.length - suffix.length))
  | .seq left (.charClass cls), input =>
      match input.reverse with
      | [] => false
      | c :: rest => decide (cls.denote c) && left.matches rest.reverse
  | .seq left right, input =>
      (List.range (input.length + 1)).any (fun split =>
        left.matches (input.take split) && right.matches (input.drop split))
  | .alt left right, input => left.matches input || right.matches input
  | .star (.charClass cls), input => input.all (fun c => decide (cls.denote c))
  | .star body, input => repeatMatches body.matches input

def Lexer.recognize (lexer : Lexer) (text : String) : Bool :=
  lexer.matches text.toList

/-- Find the longest accepted prefix, returning its spelling and the remainder.
`some ([], input)` is possible for nullable rules. A tokenizer must require
positive consumption before recursively scanning the remainder.
-/
def Lexer.longestPrefix (lexer : Lexer) (input : List Char) :
    Option (List Char × List Char) :=
  ((List.range (input.length + 1)).reverse.find? (fun n =>
    lexer.matches (input.take n))).map (fun n => (input.take n, input.drop n))

namespace Examples

def digit : Lexer := .charClass (.range '0' '9')

def letter : CharClass := .union (.range 'a' 'z') (.range 'A' 'Z')

def nameStart : CharClass := .union letter (.oneOf "-$._".toList)

def nameChar : CharClass := .union nameStart (.range '0' '9')

def bareName : Lexer := .seq (.charClass nameStart) (.star (.charClass nameChar))

def localName : Lexer := .seq (.literal "%") bareName

def integer : Lexer := .seq (.optional (.literal "-")) digit.plus

def whitespace : Lexer := (Lexer.charClass (.oneOf " \t\n\r".toList)).plus

example : integer.recognize "-123" = true := by decide
example : integer.recognize "-" = false := by decide
example : localName.recognize "%foo_42" = true := by decide
example : localName.recognize "%42" = false := by decide
example : whitespace.recognize " \t\n" = true := by decide

-- Backtracking across alternatives and repetition is essential for these.
example : (Lexer.seq (.alt (.literal "a") (.literal "ab")) (.literal "c")).recognize
    "abc" = true := by decide
example : (Lexer.star (.optional (.literal "ab"))).recognize "abab" = true := by decide
example : (Lexer.star (.literal "")).recognize "" = true := by decide
example : (Lexer.star (.literal "")).recognize "a" = false := by decide
example : integer.longestPrefix "-123xyz".toList =
    some ("-123".toList, "xyz".toList) := by decide

end Examples

end Veir.LexerLanguage
