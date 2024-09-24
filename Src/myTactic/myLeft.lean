import Lean

open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Tactic

elab "myLeft" : tactic => do
  liftMetaTactic (fun g => g.nthConstructor `left 0 (some 2))

elab "myRight" : tactic => do
  liftMetaTactic (fun g => g.nthConstructor `right 1 (some 2))

example : 1 = 1 ∨ 2 = 2 := by
  myRight;
  rfl
