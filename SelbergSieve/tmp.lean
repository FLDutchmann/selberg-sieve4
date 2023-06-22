import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Algebra.BigOperators.Basic

variable (contra:1≠1)

theorem test (a b : ℕ) : a*b=b*a :=
  by
  wlog h: a≤b
  · rw [Nat.not_le] at h
    rw [this contra b a (le_of_lt h)]
  exact Nat.mul_comm a b

#check test
    

