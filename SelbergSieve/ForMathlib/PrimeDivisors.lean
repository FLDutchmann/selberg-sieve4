/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime divisors

This file defines `primeDivisors` as an abbreviation for the support of `Nat.factorization`.
-/

namespace Nat

abbrev primeDivisors (n : ℕ) : Finset ℕ := n.factorization.support

example (n p : ℕ) (h : p ∈ n.primeDivisors) : True := by
  simp at h
  /- h : p ∈ factors n -/
  trivial

/- And if we remove simp from support_factorization: -/
attribute [-simp] Nat.support_factorization
attribute [simp] Nat.factorization_eq_zero_iff
example (n p : ℕ) (h : p ∈ n.primeDivisors) : True := by
  simp at h
  /- h : ¬↑(factorization n) p = 0 -/
  trivial


#eval (Nat.factorization 231) 

example (n : ℕ) : n.factorization = _root_.factorization n := by
    rw [Nat.factorization_eq_factors_multiset n]
    unfold _root_.factorization
  

theorem primeDivisors_eq_factors_toFinset {n : ℕ} : 
    n.primeDivisors = n.factors.toFinset := rfl

@[simp]
theorem mem_primeDivisors_of_ne_zero {n p : ℕ} (hn : n ≠ 0): 
    p ∈ n.primeDivisors ↔ p.Prime ∧ p ∣ n := by
  erw[List.mem_toFinset, Nat.mem_factors hn]

theorem mem_primeDivisors {n p : ℕ} :
    p ∈ n.primeDivisors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [mem_primeDivisors_of_ne_zero hn]
  simp? [mem_primeDivisors_of_ne_zero, ne_eq, hn, not_false_eq_true, and_true]


theorem prime_of_mem_primeDivisors {n p : ℕ} (hp : p ∈ n.primeDivisors) : p.Prime := 
  mem_primeDivisors.mp hp |>.1

theorem dvd_of_mem_primeDivisors {n p : ℕ} (hp : p ∈ n.primeDivisors) : p ∣ n := 
  mem_primeDivisors.mp hp |>.2.1

theorem pos_of_mem_primeDivisors {n p : ℕ} (hp : p ∈ n.primeDivisors) : 0 < p := 
  pos_of_mem_factorization hp

example (a b : ℕ) (h : a < b) : a ≠ b := h.ne

end Nat