import Lean
import Src.myTactic.myIntro
open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Tactic

#check evalRefl

elab "myRfl" : tactic => do
  liftMetaTactic fun goal => do goal.refl; return []


example : 1 = 1 := by myRfl

example : ∀ a : Nat, a = a := by myIntro a; myRfl
