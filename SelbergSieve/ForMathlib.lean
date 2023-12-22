/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction

namespace Aux

open BigOperators Nat.ArithmeticFunction
/- Lemmas in this file are singled out as suitible for addition to Mathlib4 with minor modifications -/


-- theorem prime_dvd_lcm_iff (a b p : ℕ) (hp : p.Prime) : p ∣ x.lcm y ↔ p ∣ x ∨ p ∣ y :=
--   ⟨ fun h => (Nat.Prime.dvd_mul hp).mp (Nat.dvd_trans h (Nat.lcm_dvd_mul x y)),
--     fun h => Or.elim h (fun hx => Trans.trans hx (Nat.dvd_lcm_left x y))
--       (fun hy => Trans.trans hy (Nat.dvd_lcm_right x y)) ⟩


theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 := by
  rw [moebius_apply_of_squarefree hl, ←pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 := by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]

theorem moebius_sq {n : ℕ} :
    μ n ^ 2 = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [Nat.isUnit_iff, zero_lt_two, pow_eq_zero_iff, moebius_eq_zero_of_not_squarefree h]

example (a b : ℕ) : a ≤ b ∨ b ≤ a := by exact Nat.le_or_le a b

variable {R : Type*}

theorem mult_lcm_eq_of_ne_zero [CommGroupWithZero R] (f : Nat.ArithmeticFunction R) (h_mult : f.IsMultiplicative) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [←h_mult.lcm_apply_mul_gcd_apply]
  field_simp

theorem prod_factors_toFinset_sdiff_of_squarefree (f : Nat.ArithmeticFunction ℝ)
  (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) {l : ℕ} :
    ∀ t : Finset ℕ, t ⊆ l.factors.toFinset → ∏ a : ℕ in t, f a = f (∏ p in t, p) :=
  by
  intro t; intro ht;
  rw [Nat.ArithmeticFunction.IsMultiplicative.map_prod _ h_mult]
  intro x hx y hy hxy
  exact (Nat.coprime_primes (Nat.prime_of_mem_factors (List.mem_toFinset.mp (ht hx)))
    (Nat.prime_of_mem_factors (List.mem_toFinset.mp (ht hy)))).mpr hxy

theorem prod_factors_of_mult (f : Nat.ArithmeticFunction ℝ) (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a : ℕ in l.factors.toFinset, f a = f l :=
  by
  rw [prod_factors_toFinset_sdiff_of_squarefree f h_mult l.factors.toFinset Finset.Subset.rfl,
    Nat.prod_factors_toFinset_of_squarefree hl]

end Aux
