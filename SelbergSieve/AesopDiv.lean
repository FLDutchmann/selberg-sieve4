/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Aesop
import SelbergSieve.Init
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction

namespace Sieve
open Finset

@[irreducible]
protected def MyDvd (a b :ℕ) : Prop := a ∣ b
open Sieve (MyDvd)

@[simp]
theorem myDvd_iff (a b : ℕ) : MyDvd a b ↔ a ∣ b := by
  unfold MyDvd
  exact Iff.rfl

macro (name := aesop_div) "aesop_div" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  {try simp_rw [←myDvd_iff] at *; aesop $c* (options := 
  { destructProductsTransparency := .reducible, applyHypsTransparency := .default, introsTransparency? := some .reducible, terminal := false } )
  (simp_options := { enabled := false})
  (rule_sets [$(Lean.mkIdent `Divisibility):ident])})


macro (name := aesop_div?) "aesop_div?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  {try simp_rw [←myDvd_iff] at *; aesop? $c* (options := 
  { destructProductsTransparency := .reducible, applyHypsTransparency := .default, introsTransparency? := some .reducible, terminal := false})
  (simp_options := { enabled := false})
  (rule_sets [$(Lean.mkIdent `Divisibility):ident])})


@[aesop safe (rule_sets [Divisibility])] 
theorem dvd_of_myDvd (a b : ℕ) : MyDvd a b → a ∣ b := (myDvd_iff a b).mp

@[aesop destruct safe (rule_sets [Divisibility])] 
theorem myDvd_of_dvd (a b : ℕ) : a ∣ b → MyDvd a b := (myDvd_iff a b).mpr

@[aesop unsafe forward 60% (rule_sets [Divisibility])] 
theorem myDvd_trans {a b c : ℕ} : MyDvd a b → MyDvd b c → MyDvd a c := by
  simp; exact Nat.dvd_trans

@[aesop safe forward (rule_sets [Divisibility])] 
theorem myDvd_of_mem_divisors {a b:ℕ} : a ∈ b.divisors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_divisors

attribute [aesop safe forward (rule_sets [Divisibility])] not_squarefree_zero

@[aesop forward safe (rule_sets [Divisibility])] 
theorem eq_zero_of_zero_myDvd (a : ℕ) : MyDvd 0 a → a = 0 := by
  simp

attribute [aesop safe (rule_sets [Divisibility])] Nat.pos_of_ne_zero

@[aesop forward safe (rule_sets [Divisibility])] 
theorem zero_mem_divisors (a : ℕ) (h : 0 ∈ a.divisors) : False := by simp at h

@[aesop forward safe (rule_sets [Divisibility])] 
theorem mem_zero_divisors (a : ℕ) (h : a ∈ Nat.divisors 0) : False := by simp at h

@[aesop forward safe (rule_sets [Divisibility])] 
theorem zero_lt_zero (h : 0 < 0) : False := by linarith

@[aesop safe (rule_sets [Divisibility])]
theorem test {n m : ℕ}: n ∣ m ∧ m ≠ 0 → n ∈ m.divisors := Nat.mem_divisors.mpr
    
@[aesop forward safe (rule_sets [Divisibility])] 
theorem dvd_of_gcd_dvd_left (a b c : ℕ) (h : MyDvd c $ a.gcd b) : MyDvd c a := myDvd_trans h (myDvd_of_dvd _ _$ Nat.gcd_dvd_left a b)
@[aesop forward safe (rule_sets [Divisibility])] 
theorem dvd_of_gcd_dvd_right (a b c : ℕ) (h : MyDvd c $ a.gcd b) : MyDvd c b := myDvd_trans h (myDvd_of_dvd _ _$ Nat.gcd_dvd_right a b)

@[aesop unsafe 50% (rule_sets [Divisibility])] 
theorem gcd_dvd_of_dvd_left (a b c : ℕ) (h : MyDvd a c) : MyDvd (a.gcd b) c := myDvd_trans (myDvd_of_dvd _ _$ Nat.gcd_dvd_left a b) h
@[aesop unsafe 50% (rule_sets [Divisibility])] 
theorem gcd_dvd_of_dvd_right (a b c : ℕ) (h : MyDvd b c) : MyDvd (a.gcd b) c := myDvd_trans (myDvd_of_dvd _ _$ Nat.gcd_dvd_right a b) h

@[aesop safe (rule_sets [Divisibility])]
theorem gcd_myDvd_left (a b : ℕ) : MyDvd (a.gcd b) a := by 
  simp; exact gcd_dvd_left a b
@[aesop safe (rule_sets [Divisibility])]
theorem gcd_myDvd_right (a b : ℕ) : MyDvd (a.gcd b) b := by 
  simp; exact gcd_dvd_right a b

@[aesop forward safe (rule_sets [Divisibility])]
theorem gcd_eq_zero_left (a b : ℕ) (h : a.gcd b = 0) : a = 0 := by 
  rw [Nat.gcd_eq_zero_iff] at h; exact h.1
@[aesop forward safe (rule_sets [Divisibility])]
theorem gcd_eq_zero_right (a b : ℕ) (h : a.gcd b = 0) : b = 0 := by 
  rw [Nat.gcd_eq_zero_iff] at h; exact h.2

@[aesop forward safe (rule_sets [Divisibility])] 
theorem dvd_of_lcm_dvd_left (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd a c := myDvd_trans (myDvd_of_dvd _ _$ Nat.dvd_lcm_left a b) h
@[aesop forward safe (rule_sets [Divisibility])] 
theorem dvd_of_lcm_dvd_right (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd b c := myDvd_trans (myDvd_of_dvd _ _$ Nat.dvd_lcm_right a b) h

@[aesop unsafe 50% (rule_sets [Divisibility])] 
theorem dvd_lcm_of_dvd_left (a b c : ℕ) (h : MyDvd c a) : MyDvd c (a.lcm b) := myDvd_trans h (myDvd_of_dvd _ _ $ Nat.dvd_lcm_left a b)
@[aesop unsafe 50% (rule_sets [Divisibility])] 
theorem dvd_lcm_of_dvd_right (a b c : ℕ) (h : MyDvd c b) : MyDvd c (a.lcm b) := myDvd_trans h (myDvd_of_dvd _ _ $ Nat.dvd_lcm_right a b)
 
@[aesop safe (rule_sets [Divisibility])]
theorem myDvd_lcm_left (a b : ℕ) : MyDvd a (a.lcm b) := by 
  simp; exact dvd_lcm_left a b
@[aesop safe (rule_sets [Divisibility])]
theorem myDvd_lcm_right (a b : ℕ) : MyDvd b (a.lcm b) := by 
  simp; exact dvd_lcm_right a b

@[aesop forward safe (rule_sets [Divisibility])]
theorem lcm_eq_zero_left (a b : ℕ) (h : a.lcm b = 0) : a = 0 ∨ b = 0 := by 
  rw [←lcm_eq_nat_lcm, lcm_eq_zero_iff] at h; exact h

attribute [aesop forward unsafe 80% (rule_sets [Divisibility])] Squarefree.squarefree_of_dvd

end Sieve

open Sieve 
example (a b c d :ℕ) (h: d ≠ 0) : (b ∈ c.divisors) → a ∣ b → c ∣ d → a ∈ d.divisors := by
  aesop_div

example (a P : ℕ) : Squarefree P → a ∈ P.divisors → a ≠ 0 := by 
  aesop_div

example (d1 d2 P : ℕ) (h0 : d1 ∣ P) (h1 : d2 ∣ P) : d1.gcd d2 ∣ P := by 
  aesop_div

example {a b c : ℕ} : a ∣ b ∧ b ∣ c → a ∣ c := by 
  aesop_div 

theorem divisors_filter_dvd {P : ℕ} (n : ℕ) (hP : P ≠ 0) (hn : n ∣ P) :
    (P.divisors.filter (· ∣ n)) = n.divisors :=
  by
  ext k; rw [Finset.mem_filter]; 
  aesop_div