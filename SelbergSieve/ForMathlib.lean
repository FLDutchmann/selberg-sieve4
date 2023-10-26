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

open scoped BigOperators Nat.ArithmeticFunction
/- Lemmas in this file are singled out as suitible for addition to Mathlib4 with minor modifications -/

  
-- theorem prime_dvd_lcm_iff (a b p : ℕ) (hp : p.Prime) : p ∣ x.lcm y ↔ p ∣ x ∨ p ∣ y := 
--   ⟨ fun h => (Nat.Prime.dvd_mul hp).mp (Nat.dvd_trans h (Nat.lcm_dvd_mul x y)), 
--     fun h => Or.elim h (fun hx => Trans.trans hx (Nat.dvd_lcm_left x y)) 
--       (fun hy => Trans.trans hy (Nat.dvd_lcm_right x y)) ⟩

example (a b : ℕ) : a ≤ b ∨ b ≤ a := by exact Nat.le_or_le a b 
 
variable {R : Type*}

theorem lcm_mul_gcd_of_mult [CommMonoidWithZero R] {f : Nat.ArithmeticFunction R} (h_mult : f.IsMultiplicative) {x y : ℕ} : 
    f x * f y = f (x.lcm y) * f (x.gcd y) := by
  by_cases hx : x = 0
  · simp only [hx, Nat.ArithmeticFunction.map_zero, zero_mul, Nat.lcm_zero_left, Nat.gcd_zero_left]
  by_cases hy : y = 0
  · simp only [hy, Nat.ArithmeticFunction.map_zero, mul_zero, Nat.lcm_zero_right, Nat.gcd_zero_right, zero_mul]
  have hgcd_ne_zero : x.gcd y ≠ 0 := Nat.gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y ≠ 0 := Nat.lcm_ne_zero hx hy
  have hfi_zero : ∀ {i},  f (i ^ 0) = 1
  · intro i; rw [pow_zero, h_mult.1]
  iterate 4 rw [h_mult.multiplicative_factorization f (by assumption),
    Finsupp.prod_of_support_subset _ (s := ((Nat.factorization x).support ⊔ (Nat.factorization y).support)) 
      _ _ (fun _ _ => hfi_zero)]
  · rw [←Finset.prod_mul_distrib, ←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _ 
    rcases Nat.le_or_le (Nat.factorization x p) (Nat.factorization y p) with h | h <;> 
    simp only [Nat.factorization_lcm hx hy, ge_iff_le, Finsupp.sup_apply, h, sup_of_le_right, 
      sup_of_le_left, inf_of_le_right, Nat.factorization_gcd hx hy, Finsupp.inf_apply, inf_of_le_left, 
      mul_comm]
  · rw [Nat.factorization_gcd hx hy, Finsupp.support_inf, Finset.sup_eq_union]
    apply Finset.inter_subset_union
  · rw [Nat.factorization_lcm hx hy, Finsupp.support_sup, Finset.sup_eq_union]
  · apply Finset.subset_union_right
  · apply Finset.subset_union_left

theorem mult_lcm_eq_of_ne_zero [CommGroupWithZero R] (f : Nat.ArithmeticFunction R) (h_mult : f.IsMultiplicative) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) : 
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [lcm_mul_gcd_of_mult h_mult]
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