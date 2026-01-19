import Veir

def count := 50_000

def getCountFrom (c : Option String) :=
  match c with
  | none => count
  | some s =>
    match s.toNat? with
    | none => count
    | some n => n

def getPCFrom (c : Option String) :=
  match c with
  | none => 100
  | some s =>
    match s.toNat? with
    | none => 100
    | some n => n

def bench (f: IO Unit) (count : Nat) : IO Unit := do
  let startTime ← IO.monoMsNow
  f
  let endTime ← IO.monoMsNow
  let elapsedTime := endTime - startTime
  IO.println s!"Elapsed time: {elapsedTime} miliseconds"
  IO.println s!"ns per op : {(elapsedTime * 1000 * 1000) / count}"

def main (args : List String) : IO Unit := do
  IO.println s!"Buffed Benchmark ({args})"
  let count := getCountFrom args[1]?
  match args[0]? with
  | some bench => Veir.Benchmarks.runBenchmark bench count (getPCFrom args[2]?)
  | _ => IO.println "Please provide a benchmark name"
