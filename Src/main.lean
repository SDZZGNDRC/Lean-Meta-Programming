
inductive Result where
  | StrResult (s : String) : Result
  | NatResult (num : Nat) : Result
  deriving Repr

open Result in
def checkEven := fun i => match i with
  | 0 => StrResult "Even"
  | n + 1 => match checkEven n with
            | StrResult s => StrResult s
            | NatResult n => NatResult n

def isEven := fun i =>
  match i with
  | 0 => true
  | n + 1 => match isEven n with
            | true => false
            | false => true

#reduce isEven 0
#reduce isEven 1
#reduce isEven 2




#reduce checkEven 0
#reduce checkEven 10

def main : IO Unit := do
  IO.println s!"Hello, world!"
