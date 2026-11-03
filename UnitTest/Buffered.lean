module

import Veir.Input
import Veir.Buffered
import Veir.Parser.Buffered

/-! The upstream and buffered parsers must coexist without duplicate declarations,
attribute registrations, or accidental opcode/typeclass resolution across backends.
`testParsers` runs in the native `parser-tests` executable: ExArray's static C FFI is not
available to Lean's `#eval` interpreter. -/

public section
namespace UnitTest.Buffered

private def source : ByteArray := r#"
"builtin.module"() ({
  "test.test"(%later) : (i32) -> ()
  %later = "test.test"() : () -> i32
}) : () -> ()
"#.toUTF8

def testParsers : IO Unit := do
  match Veir.Input.parseSourceString source (verifyAfterParse := false) with
  | .error error => throw (IO.userError s!"upstream parser: {error}")
  | .ok _ => pure ()
  match Veir.Parser.parseSourceString source with
  | .error error => throw (IO.userError s!"buffered parser: {error}")
  | .ok _ => pure ()

example {content : ByteArray} {ctx : Veir.Buffered.Parser.StaticIR.Context}
    {op : Veir.Buffered.Parser.IR.Op} {info : Veir.Buffered.Parser.SourceInfo}
    (h : Veir.Parser.parseSourceString content = .ok (ctx, op, info)) :
    ctx.spec.WellFormed ∧ op.InBounds ctx.toIRContext :=
  Veir.Parser.parseSourceString_safe h

end UnitTest.Buffered
