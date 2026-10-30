module
public import Veir.Passes.RegisterAllocation.RegisterStack
meta import Veir.Passes.RegisterAllocation.RegisterStack

open Veir

/-! Test RegisterStack -/

/-! Fresh stack is empty -/
#guard (default : RegisterStack).free = []

/-! Fresh stack starts at index 0 -/
#guard (default : RegisterStack).next = 0

/-! First allocated registers have indices -1 and -2, stack remains empty -/
#guard Id.run do
  let (first, stack) := (default : RegisterStack).pop
  let (second, stack) := stack.pop
  return first.index == some (-1) && second.index == some (-2) &&
    stack.next == 2 && stack.free.isEmpty

/-! Registers that are pushed on the stack are reused -/
#guard Id.run do
  let (first, stack) := (default : RegisterStack).pop
  let (second, stack) := stack.pop
  let stack := (stack.push first).push second
  let (reusedSecond, stack) := stack.pop
  let (reusedFirst, stack) := stack.pop
  let (fresh, stack) := stack.pop
  return reusedSecond == second && reusedFirst == first &&
    fresh.index == some (-3) && stack.next == 3 && stack.free.isEmpty
