import Lean

open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Tactic

#check Lean.Parser.Tactic.rwRule
#check evalRewriteSeq
#check Lean.MVarId.rewrite
#check rewriteTarget
#check Lean.Expr.instantiate
#check evalExact


elab "myRw" h:ident : tactic => do
    let goal ← getMainGoal
    let type ← goal.getType
    if type.isForall then
      let (_, mvarIds) ← liftMetaMAtMain fun mvarId => do
        let (fvarId, mvarId) ← mvarId.intro h.getId
        pure (fvarId, [mvarId])
      replaceMainGoal mvarIds
