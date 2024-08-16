import Lean
open Lean Meta

def z := Expr.const ``Nat.zero []
#eval z -- Lean.Expr.const `Nat.zero []

def natExpr : Nat → Expr
| 0 => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]
-- exercise 1
#eval sumExpr 1 2
elab "one" : term => return sumExpr 1 2
#check one
#reduce one

-- exercise 2
def one_plus_two := Expr.app (Expr.app (Expr.const ``Nat.add []) (Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])))
                    (Expr.app (Expr.const ``Nat.succ []) (Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])))
#eval one_plus_two
elab "two" : term => return one_plus_two
#reduce two


-- exercise 3
#eval Expr.lam `x (.const `Nat []) (.app (.app (.const ``Nat.add []) (natExpr 1)) (.bvar 0)) .default
elab "three" : term => return Expr.lam `x (.const `Nat []) (.app (.app (.const ``Nat.add []) (natExpr 1)) (.bvar 0)) .default
#check three
#reduce three 6

-- exercise 4
def four : Expr := Expr.lam `a (.const `Nat [])
      (
        .lam `b (.const `Nat [])
        (
          .lam `c (.const `Nat [])
          (
              .app
              (
                .app (.const ``Nat.add [])
                (
                  .app (.app (.const ``Nat.mul []) (.bvar 1)) (.bvar 2)
                )
              )
              (.bvar 0)
          )
          .default) .default) .default
elab "four" : term => return four
#check four
#reduce four 666 1 2


-- exercise 5
def five := Expr.lam `x (.const `Nat []) (.lam `y (.const `Nat []) (.app (.app (.const ``Nat.add []) (.bvar 1)) (.bvar 0)) .default) .default
elab "five" : term => return five
#check five
#reduce five 4 5

-- exercise 6
def six := Expr.lam `x (.const `String []) (.app (.app (.const `String.append []) (.lit (.strVal "hello, "))) (.bvar 0)) .default

elab "six" : term => return six
#check six
#eval six "world"


-- exercise 7
def seven := Expr.forallE `x (.sort Lean.Level.zero) (.app (.app (.const `And []) (.bvar 0)) (.bvar 0)) .default
elab "seven" : term => return seven

#check seven
#reduce seven

-- exercise 8
def eight := Expr.forallE `x (.const `Nat []) (.const `String []) .default
elab "eight" : term => return eight
#check eight
#reduce eight


-- exercise 9
def nine := Expr.lam `p (Expr.sort Lean.Level.zero) (Expr.lam `hP (.bvar 1) (.bvar 0) .default) .default
elab "nine" : term => return nine
#check nine
#reduce nine

-- exercise 10
def ten := Expr.sort (Nat.toLevel 7)
elab "ten" : term => return ten
#check ten
#reduce ten
