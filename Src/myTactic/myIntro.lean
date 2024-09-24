import Lean

open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Tactic


elab "myIntro" h:ident : tactic => do
    let goal ← getMainGoal
    let type ← goal.getType
    if type.isForall then
      let mvarIds ← liftMetaMAtMain fun mvarId => do
        let (_, mvarId) ← mvarId.intro h.getId
        pure [mvarId]
      replaceMainGoal mvarIds

#check evalIntro

example : 1 = 1 := by
  myIntro a
  sorry


example : ∀ a : Nat, a = a := by
  myIntro x
  sorry

example : ∀ a : Nat, a = a → a = a := by
  myIntro h
  myIntro h'
  sorry



example : ∀ a : Nat, a = a → a = a := by
  intro h
  intro h'
  sorry
