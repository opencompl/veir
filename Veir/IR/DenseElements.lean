module

public import Veir.IR.Attribute

namespace Veir

/-!
  Reading the integers of a dense elements attribute, which VeIR keeps as text.
-/

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def denseInteger? (text : String) : Option Int := do
  if text == "true" then return 1
  if text == "false" then return 0
  if text.startsWith "0x" then
    let digits := text.toList.drop 2
    guard (!digits.isEmpty)
    let n ← digits.foldlM (fun n c => do return n * 16 + (← hexDigit? c)) 0
    return Int.ofNat n
  text.toInt?

/-- Decode the byte-aligned integer form of MLIR's little-endian raw dense data.
    A single element's bytes can encode a splat. Other raw encodings stay unhandled. -/
private def denseRawIntegers? (text : String) (width count : Nat) : Option (Array Int) := do
  guard (width > 0 && width % 8 == 0 && text.startsWith "\"0x" && text.endsWith "\"")
  let chars := (text.toList.drop 3).dropLast.toArray
  let bytesPerElement := width / 8
  guard (chars.size == 2 * bytesPerElement * count || chars.size == 2 * bytesPerElement)
  let mut values := #[]
  for i in 0...chars.size / (2 * bytesPerElement) do
    let mut value := 0
    for j in 0...bytesPerElement do
      let k := 2 * (i * bytesPerElement + j)
      let hi ← hexDigit? chars[k]!
      let lo ← hexDigit? chars[k + 1]!
      value := value + (hi * 16 + lo) * 2 ^ (8 * j)
    values := values.push (Int.ofNat value)
  return if values.size == 1 then Array.replicate count values[0]! else values

/--
  The integers of a dense elements attribute whose type is a tensor or vector of shape `dims`
  with `width`-bit integer elements, or `none` if its type has another shape or element type,
  or its body cannot be read. VeIR keeps dense elements as text, so this reads integer lists,
  splats and byte-aligned raw hex data, and checks each value is in MLIR's range for the width:
  from the signed minimum to the unsigned maximum.
-/
public def DenseElementsAttr.integers? (attr : DenseElementsAttr) (dims : List Nat)
    (width : Nat) : Option (Array Int) := do
  guard (!dims.isEmpty)
  let shape := String.intercalate "x" (dims.map toString ++ [s!"i{width}"])
  let attrType := String.ofList (attr.type.toList.filter (!·.isWhitespace))
  guard (attrType == s!"tensor<{shape}>" || attrType == s!"vector<{shape}>")
  let count := dims.foldl (· * ·) 1
  let text := String.ofList (attr.value.toList.filter (!·.isWhitespace))
  if text.isEmpty then
    guard (count == 0)
    return #[]
  if text.startsWith "\"" then return ← denseRawIntegers? text width count
  let values ← if text.startsWith "[" then do
      let flat := String.ofList (text.toList.filter fun c => c != '[' && c != ']')
      if flat.isEmpty then pure #[]
      else (flat.splitOn ",").toArray.mapM denseInteger?
    else do
      let value ← denseInteger? text
      pure (Array.replicate count value)
  guard (values.size == count)
  guard (values.all fun v => -(2 ^ (width - 1) : Int) ≤ v && v < (2 ^ width : Int))
  return values

end Veir
