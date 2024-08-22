import Lean

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

#eval pure (.*.) <*> some 4 <*> some 5
#eval (.*.) <$> some 4 <*> some 5

#check List.bind
#check Functor.map
#check Seq.seq
#check SeqLeft.seqLeft

instance : Applicative List where
  pure := List.pure
  seq f x := List.bind f fun y => y <$> (x ())

#check Seq.seq

#synth Applicative List

#eval [(·+2)] <*> [4,6]

#eval (some (.+1)) <*> (some 2)

#check List.bind

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)


def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())


def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)


instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i

#eval increment 1 0
#check mapM increment
#check mapM
#eval mapM increment [1, 2, 3, 4, 5] 0

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
  deriving Repr

def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}


instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}


def isEven (i : Int) : Bool :=
  i % 2 == 0

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
   else pure ()) >>= fun () =>
  pure i

#reduce mapM saveIfEven [1, 2, 3, 4, 5]

#eval mapM saveIfEven [1, 2, 3, 4, 5]

-- Exercise 1
-- Mapping on a Tree
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
  deriving Repr

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | leaf => pure leaf
  | branch l a r => f a >>= fun a' =>
    BinTree.mapM f l >>= fun l' =>
    BinTree.mapM f r >>= fun r' =>
    pure (branch l' a' r')

open BinTree in
def mapM_test : BinTree Nat :=
  branch (branch leaf 1 leaf) 2 (branch leaf 3 leaf)

def mapM_f : Nat → WithLog Nat Unit := fun n =>
  { log := [n], val := () }

#check mapM_test
#eval BinTree.mapM mapM_f mapM_test


-- The Option Monnad Concat


-- 5.2 Example: Arithmetic in Monads

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op


inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))

def applyPrimOption : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      none
    else pure (x / y)

def applyPrimExcept : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int): Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2


#eval evaluateM applyPrimOption fourteenDivided
#eval evaluateM applyPrimExcept fourteenDivided

namespace hidden

def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def evaluateM [Monad m] (applyDiv : Int → Int → m Int): Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyDiv e1 >>= fun v1 =>
    evaluateM applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2

#eval evaluateM applyDivOption fourteenDivided
#eval evaluateM applyDivExcept fourteenDivided

end hidden


namespace hidden_2

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2

def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))


def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind (m : Reader ρ α) (f : α → Reader ρ β) : Reader ρ β := fun env =>
  f (m env) env

/-
Reader.bind (Reader.pure v) f
===>
Reader.bind (fun _ => v) f
===>
fun env => f ((fun _ => v) env) env
===>
fun env => f v env
===>
f v
-/

instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int := fun env =>
  match env.lookup op with
  | none => 0
  | some f => f x y
  -- read >>= fun env =>
  -- match env.lookup op with
  -- | none => pure 0
  -- | some f => pure (f x y)


open Expr Prim in
#eval evaluateM applyPrimReader (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv




end hidden_2

namespace hidden_3



end hidden_3




-- 5.4 The IO Monad

#print Nat
#print Char.isAlpha
#print List.isEmpty


#print IO
#print IO.Error
#print EIO
#print EStateM
#print EStateM.Result

#print EStateM.bind

#print IO.RealWorld


namespace hidden_4
#print Lean.Meta.evalExprCore

end hidden_4
