import Aesop
import SelbergSieve.Init
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction

namespace Sieve
open Finset

macro (name := aesop_div) "aesop_div" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (options := { introsTransparency? := some .default, terminal := false } )
  (simp_options := { enabled := false})
  (rule_sets [$(Lean.mkIdent `Divisibility):ident]))


macro (name := aesop_div?) "aesop_div?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c* (options := { introsTransparency? := some .default, terminal := false})
  (simp_options := { enabled := false})
  (rule_sets [$(Lean.mkIdent `Divisibility):ident]))


attribute [aesop unsafe forward 60% (rule_sets [Divisibility])] Nat.dvd_trans
attribute [aesop safe forward (rule_sets [Divisibility])] Nat.dvd_of_mem_divisors
attribute [aesop safe forward (rule_sets [Divisibility])] not_squarefree_zero

@[aesop forward safe (rule_sets [Divisibility])] 
theorem eq_zero_of_zero_dvd (a : ℕ) : 0 ∣ a → a = 0 := by
  apply zero_dvd_iff.mp

attribute [aesop safe (rule_sets [Divisibility])] Nat.pos_of_ne_zero

@[aesop forward safe (rule_sets [Divisibility])] 
theorem zero_mem_divisors (a : ℕ) (h : 0 ∈ a.divisors) : a = 0 := by simp at h

@[aesop forward safe (rule_sets [Divisibility])] 
theorem zero_lt_zero (h : 0 < 0) : False := by linarith

@[aesop safe (rule_sets [Divisibility])]
theorem test {n m : ℕ}: n ∣ m ∧ m ≠ 0 → n ∈ m.divisors := Nat.mem_divisors.mpr
    
@[aesop forward safe (rule_sets [Divisibility])] 
theorem dvd_of_gcd_dvd_left (a b c : ℕ) (h : c ∣ a.gcd b) : c ∣ a := Trans.trans h (Nat.gcd_dvd_left a b)
@[aesop forward safe (rule_sets [Divisibility])] 
theorem dvd_of_gcd_dvd_right (a b c : ℕ) (h : c ∣ a.gcd b) : c ∣ b := Trans.trans h (Nat.gcd_dvd_right a b)

@[aesop unsafe 50% (rule_sets [Divisibility])] 
theorem gcd_dvd_of_dvd_left (a b c : ℕ) (h : a ∣ c) : a.gcd b ∣ c := Trans.trans (Nat.gcd_dvd_left a b) h
@[aesop unsafe 50% (rule_sets [Divisibility])] 
theorem gcd_dvd_of_dvd_right (a b c : ℕ) (h : b ∣ c) : a.gcd b ∣ c := Trans.trans (Nat.gcd_dvd_right a b) h

@[aesop forward safe (rule_sets [Divisibility])] 
theorem dvd_of_lcm_dvd_left (a b c : ℕ) (h : a.lcm b ∣ c) : a ∣ c := Trans.trans (Nat.dvd_lcm_left a b) h
@[aesop forward safe (rule_sets [Divisibility])] 
theorem dvd_of_lcm_dvd_right (a b c : ℕ) (h : a.lcm b ∣ c) : b ∣ c := Trans.trans (Nat.dvd_lcm_right a b) h

@[aesop unsafe 50% (rule_sets [Divisibility])] 
theorem dvd_lcm_of_dvd_left (a b c : ℕ) (h : c ∣ a) : c ∣ a.lcm b := Trans.trans h (Nat.dvd_lcm_left a b)
@[aesop unsafe 50% (rule_sets [Divisibility])] 
theorem dvd_lcm_of_dvd_right (a b c : ℕ) (h : c ∣ b) : c ∣ a.lcm b := Trans.trans h (Nat.dvd_lcm_right a b)

attribute [aesop forward unsafe 80% (rule_sets [Divisibility])] Squarefree.squarefree_of_dvd

  
example (a b c d :ℕ) (h: d ≠ 0) : (b ∈ c.divisors) → a ∣ b → c ∣ d → a ∈ d.divisors := by
  aesop_div?

example (a P : ℕ) : Squarefree P → a ∈ P.divisors → a ≠ 0 := by 
  aesop_div?

example (d1 d2 P : ℕ) (h0 : d1 ∣ P) (h1 : d2 ∣ P) : d1.gcd d2 ∣ P := by aesop_div?

end Sieve