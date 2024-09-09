import Lean

/-
https://leetcode.cn/problems/median-of-two-sorted-arrays/description/
-/

def median (nums : List Int) : Float :=
  if nums.length % 2 == 0 then
    let mid := nums.length / 2
    Float.ofInt (nums.get! mid + nums.get! (mid - 1)) / 2.0
  else
    let mid := nums.length / 2
    Float.ofInt <| nums.get! mid

#eval median [1,2,3,4]

#check optParam


#check List.get
