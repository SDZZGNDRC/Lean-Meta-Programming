import Lean

open Lean Lean.Expr Lean.Meta

#eval show MetaM Unit from do
  -- Create two fresh metavariables of type `Nat`.
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  -- Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  -- creates a function type.
  let mvar3 ← mkFreshExprMVar (← mkArrow (.const ``Nat []) (.const ``Nat []))
    (userName := `mvar3)

  -- Define a helper function that prints each metavariable.
  let printMVars : MetaM Unit := do
    IO.println s!"  meta1: {← instantiateMVars mvar1}"
    IO.println s!"  meta2: {← instantiateMVars mvar2}"
    IO.println s!"  meta3: {← instantiateMVars mvar3}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  mvar1.mvarId!.assign (.app mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  mvar2.mvarId!.assign (.const ``Nat.zero [])
  IO.println "After assigning mvar2:"
  printMVars

  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  mvar3.mvarId!.assign (.const ``Nat.succ [])
  IO.println "After assigning mvar3:"
  printMVars
-- Initially, all metavariables are unassigned:
--   meta1: ?_uniq.1
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar1:
--   meta1: ?_uniq.3 ?_uniq.2
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar2:
--   meta1: ?_uniq.3 Nat.zero
--   meta2: Nat.zero
--   meta3: ?_uniq.3
-- After assigning mvar3:
--   meta1: Nat.succ Nat.zero
--   meta2: Nat.zero
--   meta3: Nat.succ


def myAssumption (mvarId : MVarId) : MetaM Bool := do
  -- Check that `mvarId` is not already assigned.
  mvarId.checkNotAssigned `myAssumption
  -- Use the local context of `mvarId`.
  mvarId.withContext do
    -- The target is the type of `mvarId`.
    let target ← mvarId.getType
    -- For each hypothesis in the local context:
    for ldecl in ← getLCtx do
      -- If the hypothesis is an implementation detail, skip it.
      if ldecl.isImplementationDetail then
        continue
      -- If the type of the hypothesis is definitionally equal to the targetd
      -- type:
      if ← isDefEq ldecl.type target then
        -- Use the local hypothesis to prove the goal.
        mvarId.assign ldecl.toExpr
        -- Stop and return true.
        return true
    -- If we have not found any suitable local hypothesis, return false.
    return false



def someNumber : Nat := (· + 2) $ 3

#eval Expr.const ``someNumber []

#eval reduce (Expr.const ``someNumber [])


def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def irreducibleDef : Nat      := 1
def                defaultDef     : Nat      := irreducibleDef + 1
abbrev             reducibleDef   : Nat      := defaultDef + 1

#eval traceConstWithTransparency .reducible ``reducibleDef

set_option pp.explicit true
#eval traceConstWithTransparency .reducible ``reducibleDef
set_option pp.explicit false


#eval traceConstWithTransparency .instances ``reducibleDef

#eval traceConstWithTransparency .default ``reducibleDef

#eval traceConstWithTransparency .all ``reducibleDef


open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

#eval whnf' `(List.cons 1 [])

#eval whnf' `(List.cons (1 + 1) [])

#eval withTransparency .reducible $ whnf' `(List.append [1] [2])

#eval whnf' `(λ x : Nat => x)

def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) Q) => return some (P, Q)
  | _ => return none



def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- Check that the goal is not yet assigned.
  goal.checkNotAssigned `myApply
  -- Operate in the local context of the goal.
  goal.withContext do
    -- Get the goal's target type.
    let target ← goal.getType
    -- Get the type of the given expression.
    let type ← inferType e
    -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `type` does
    -- not have this form, `args` is empty and `conclusion = type`.)
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    -- If the conclusion unifies with the target:
    if ← isDefEq target conclusion then
      -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
      -- metavariables in `args`.
      goal.assign (mkAppN e args)
      -- `isDefEq` may have assigned some of the `args`. Report the rest as new
      -- goals.
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    -- If the conclusion does not unify with the target, throw an error.
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"


elab "myApply" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a



-- exercise 1
-- #eval show MetaM Unit from do
run_meta do
  -- Create a fresh metavariable of type `Nat`.
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)

  -- Define a helper function that prints the mvar.
  let printMvar : MetaM Unit := do
    IO.println s!"  mvar: {← instantiateMVars mvar1}"

  IO.println "Initially, metavariable is unassigned:"
  printMvar

  -- Assign `mvar1` to `Nat.zero`.
  mvar1.mvarId!.assign <| mkNatLit <| 3
  IO.println "After assigning mvar1:"
  printMvar


-- exercise 2
run_meta do
  IO.println s!"{ ←instantiateMVars (mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2])}"


-- exercise 3
run_meta do
  let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
  let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  let mvar3 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar3)

  let printMVars : MetaM Unit := do
    -- IO.println s!"  meta1: {mvar1}"
    -- IO.println s!"  meta2: {mvar2}"
    -- IO.println s!"  meta3: {mvar3}"
    IO.println s!"  meta1: {← instantiateMVars mvar1}"
    IO.println s!"  meta2: {← instantiateMVars mvar2}"
    IO.println s!"  meta3: {← instantiateMVars mvar3}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  mvar1.mvarId!.assign <| Expr.app (app (.const `Nat.add []) (mkAppN (.const `Nat.add []) #[twoExpr, mvar2])) mvar3

  IO.println "After assigning mvar1:"
  printMVars

  mvar3.mvarId!.assign oneExpr

  IO.println "After assigning mvar3:"
  printMVars


-- exercise 4
elab "explore" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  IO.println "Our metavariable"
  IO.println s!"  type: {← instantiateMVars metavarDecl.type}"
  IO.println s!"  userName: {metavarDecl.userName}"

  IO.println "All of its local declarations"
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    IO.println s!"  type : {← instantiateMVars ldecl.type}"
    IO.println s!"  userName : {ldecl.userName}"


-- exercise 5
elab "solve" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal

  mvarId.checkNotAssigned `solve

  mvarId.withContext do
    let target ← mvarId.getType
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      if ← isDefEq ldecl.type target then
        mvarId.assign ldecl.toExpr
        return


theorem red (_ : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  solve


-- exercise 6
-- a)
def sixA : Bool → Bool := fun x => x
#eval reduce (Expr.const `sixA [])
-- b)
def sixB : Bool := (fun x => x) ((true && false) || true)
#eval Lean.Meta.reduce (Expr.const `sixB [])
-- c)
def sixC : Nat := 800 + 2
#eval Lean.Meta.reduce (Expr.const `sixC [])


-- exercise 7
#eval show MetaM Unit from do
  let litExpr := Expr.lit (Lean.Literal.natVal 1)
  let standardExpr := Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])

  let isEqual ← Lean.Meta.isDefEq litExpr standardExpr
  IO.println isEqual


-- exercise 8
-- a) true
def eightA := (fun _ => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))
#eval show MetaM Unit from do
  let expr1 := Lean.mkNatLit 5
  let expr2 := Expr.const `eightA []
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

-- b) true
#eval show MetaM Unit from do
  let expr1 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, Lean.mkNatLit 1]
  let expr2 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, Lean.mkNatLit 2]
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

-- c) false
#eval show MetaM Unit from do
  let expr1 ← Lean.Meta.mkFreshExprMVar (Expr.const `String []) (userName := `expr1)
  let expr2 := Lean.mkNatLit 2
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

-- d) true
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar Option.none (userName := `a)
  let b ← Lean.Meta.mkFreshExprMVar Option.none (userName := `b)
  let expr1 := Lean.mkAppN (Expr.const `Nat.add []) #[a, Expr.const `Int []]
  let expr2 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkStrLit "hi", b]
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

  IO.println s!"a: {← instantiateMVars a}"
  IO.println s!"b: {← instantiateMVars b}"

-- e)
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `a)
  let expr1 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, a]
  let expr2 := Lean.mkNatLit 3
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

-- f) true
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `a)
  let expr1 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, a]
  let expr2 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, Lean.mkNatLit 1]
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

  IO.println s!"a: {← instantiateMVars a}"

-- ?? exercise 9
@[reducible] def reducibleDef_     : Nat := 1 -- same as `abbrev`
@[instance] def instanceDef       : Nat := 2 -- same as `instance`
def defaultDef_                    : Nat := 3
@[irreducible] def irreducibleDef_ : Nat := 4

@[reducible] def sum := [reducibleDef_, instanceDef, defaultDef_, irreducibleDef_]

#eval show MetaM Unit from do
  let constantExpr := Expr.const `sum []

  Meta.withTransparency Meta.TransparencyMode.reducible do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.instances do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.default do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.all do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  let reducedExpr ← Meta.reduce constantExpr
  dbg_trace (← ppExpr reducedExpr) -- ...


-- ?? exercise 10
-- Non-idiomatic: we can only use `Lean.mkAppN`.
def tenA : MetaM Expr := do
  let body := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, Expr.bvar 0]
  return Expr.lam `x (Expr.const `Nat []) body BinderInfo.default

-- ?? Idiomatic: we can use both `Lean.mkAppN` and `Lean.Meta.mkAppM`.
def tenB : MetaM Expr := do
  Lean.Meta.withLocalDecl `x .default (Expr.const `Nat []) (fun x => do
    -- let body := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, x]
    let body ← Lean.Meta.mkAppM `Nat.add #[Lean.mkNatLit 1, x]
    Lean.Meta.mkLambdaFVars #[x] body
  )

#eval show MetaM _ from do
  ppExpr (← tenA) -- fun x => Nat.add 1 x
#eval show MetaM _ from do
  ppExpr (← tenB) -- fun x => Nat.add 1 x


-- exercise 11
def eleven : MetaM Expr :=
  return Expr.forallE `yellow (Expr.const `Nat []) (Expr.bvar 0) BinderInfo.default

#eval show MetaM _ from do
  dbg_trace (← eleven) -- forall (yellow : Nat), yellow


-- ?? exercise 12


-- ?? exercise 13


-- ?? exercise 14
#eval show Lean.Elab.Term.TermElabM _ from do
  let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
  let expr ← Elab.Term.elabTermAndSynthesize stx none

  let (_, _, conclusion) ← forallMetaTelescope expr
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← lambdaMetaTelescope expr
  dbg_trace conclusion -- ...


-- ?? exercise 15
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `String []) (userName := `a)
  let b ← Lean.Meta.mkFreshExprMVar (Expr.sort (Nat.toLevel 1)) (userName := `b)
  -- ?a + Int
  let c := Lean.mkAppN (Expr.const `Nat.add []) #[a, Expr.const `Int []]
  -- "hi" + ?b
  let d := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkStrLit "hi", b]

  IO.println s!"value in c: {← instantiateMVars c}" -- Nat.add ?_uniq.1 Int
  IO.println s!"value in d: {← instantiateMVars d}" -- Nat.add String ?_uniq.2

  let state : SavedState ← saveState
  IO.println "\nSaved state\n"

  if ← Lean.Meta.isDefEq c d then
    IO.println true
    IO.println s!"value in c: {← instantiateMVars c}"
    IO.println s!"value in d: {← instantiateMVars d}"

  restoreState state
  IO.println "\nRestored state\n"

  IO.println s!"value in c: {← instantiateMVars c}"
  IO.println s!"value in d: {← instantiateMVars d}"
