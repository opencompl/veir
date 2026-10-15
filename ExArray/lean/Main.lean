import ExArray

def main : IO Unit := do
  let a := ExArray.empty.extend 12
  let b := a.blit32 4 0x0C
  unless a.read64 0 == 0 && b.read64 0 == 0x0000000C00000000 do
    throw (IO.userError "copy/read/write check failed")
  let c := b.blit64 0 123456789
  unless c.read64 0 == 123456789 do
    throw (IO.userError "64-bit check failed")
  let d := ExArray.empty.push 42 (by decide)
  unless d.uget 0 (by simp only [d, ExArray.push_size]; decide) == 42 && d.usize == 1 do
    throw (IO.userError "push check failed")
  IO.println "ExArray tests passed"
