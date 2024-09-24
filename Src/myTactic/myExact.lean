import Lean
import Src.myTactic.myIntro
open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Tactic

#check evalExact

elab "myExact" e:term : tactic => do
  closeMainGoalUsing `myExact fun type => do
    let r ← elabTermEnsuringType e type
    return r

example (h : 1 = 1) : 1 = 1 := by
  myExact h

example : ∀ a : Nat, a = a → a = a := by
  myIntro a
  myIntro h
  myExact h
