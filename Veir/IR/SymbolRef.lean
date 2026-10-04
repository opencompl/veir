module

public import Veir.IR.Attribute
import Veir.ForLean

namespace Veir

/-- Decode the same quoted-name escapes accepted by the MLIR lexer. -/
private def decodeSymbolEscapes (acc : ByteArray) : List Char → Option ByteArray
  | [] => some acc
  | '\\' :: '\\' :: rest => decodeSymbolEscapes (acc.push 0x5C) rest
  | '\\' :: '"' :: rest => decodeSymbolEscapes (acc.push 0x22) rest
  | '\\' :: 'n' :: rest => decodeSymbolEscapes (acc.push 0x0A) rest
  | '\\' :: 't' :: rest => decodeSymbolEscapes (acc.push 0x09) rest
  | '\\' :: hi :: lo :: rest => do
    let hi ← Char.hexDigit? hi
    let lo ← Char.hexDigit? lo
    decodeSymbolEscapes (acc.push (hi * 16 + lo)) rest
  | '\\' :: _ => none
  | c :: rest => decodeSymbolEscapes (acc ++ c.toString.toUTF8) rest

/-- Canonical symbol bytes, matching the decoded `sym_name` of a definition. -/
public def FlatSymbolRefAttr.getName? (ref : FlatSymbolRefAttr) : Option ByteArray := do
  let some name := ref.value.dropPrefix? "@" | none
  let name := name.toString
  if name.startsWith "\"" then
    if !name.endsWith "\"" then return ← none
    let chars := ((name.drop 1).dropEnd 1).toString.toList
    decodeSymbolEscapes ByteArray.empty chars
  else
    some name.toUTF8

end Veir
