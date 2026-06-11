import ExArray

def main : IO Unit :=
  let a := ExArray.empty
  let a := a.extend 12
  let a := a.blit32 4 12
  let x := a.read64 0
  IO.println s!"Result is {x}"
