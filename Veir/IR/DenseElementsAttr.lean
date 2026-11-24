module

public import Veir.IR.Attribute
import Veir.ForLean
import Veir.Parser.Parser

namespace Veir

/--
  Read one signless integer dense element, using MLIR's literal syntax and range:
  `true` or `false` for `i1`, or an optionally negated decimal or `0x`-prefixed integer.
  Positive values may reach the unsigned maximum; negative values must reach no further
  than the signed minimum. A negative zero is rejected, as in `buildAttributeAPInt`.
-/
public def DenseElementsAttr.parseInteger? (text : String) (width : Nat) : Option Int := do
  let text := text.trimAscii.toString
  if width == 1 && text == "true" then return 1
  if width == 1 && text == "false" then return 0
  let negative := text.startsWith "-"
  let digits := if negative then (text.drop 1).trimAscii.toString else text
  guard (digits.startsWith "0x" || digits.toList.all Char.isDigit)
  let n ← Parser.numericValueToNat? digits.toUTF8
  if negative then
    guard (0 < width && 1 ≤ n && n ≤ 2 ^ (width - 1))
    return -(n : Int)
  guard (n < 2 ^ width)
  return n

/--
  Decode a raw dense elements body, `"0x..."`, as `count` unsigned `width`-bit patterns.
  As in MLIR's `DenseElementsAttr::getFromRawBuffer`, each element takes
  `⌈width / 8⌉` little-endian bytes, and a buffer holding a single element is a splat.
  For `i1`, any nonzero byte represents `true`, as in MLIR's boolean decoding.
  The caller checks the attribute's shape and supplies its element count and integer width.
  Returns `none` for malformed hex or a buffer whose size fits neither form.
-/
public def DenseElementsAttr.parseRawIntegers? (body : String) (count width : Nat) :
    Option (Array Nat) := do
  let digits ← (body.dropPrefix? "\"0x").bind (·.dropSuffix? "\"")
  let digits ← digits.toString.toList.toArray.mapM Char.hexDigit?
  guard (digits.size % 2 == 0)
  let bytes := (Array.range (digits.size / 2)).map fun i =>
    digits[2 * i]!.toNat * 16 + digits[2 * i + 1]!.toNat
  let stride := (width + 7) / 8
  let element (i : Nat) : Nat :=
    let value := (List.range stride).foldr (fun j acc => acc * 256 + bytes[i * stride + j]!) 0
    if width == 1 then (if value == 0 then 0 else 1) else value % 2 ^ width
  if bytes.size == stride then
    return Array.replicate count (element 0)
  guard (bytes.size == stride * count)
  return (Array.range count).map element

end Veir
