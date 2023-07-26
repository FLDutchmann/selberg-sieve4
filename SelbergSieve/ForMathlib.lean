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

  
theorem prime_dvd_lcm_iff (a b p : ℕ) (hp : p.Prime) : p ∣ x.lcm y ↔ p ∣ x ∨ p ∣ y := 
  ⟨ fun h => (Nat.Prime.dvd_mul hp).mp (Nat.dvd_trans h (Nat.lcm_dvd_mul x y)), 
    fun h => Or.elim h (fun hx => Trans.trans hx (Nat.dvd_lcm_left x y)) 
      (fun hy => Trans.trans hy (Nat.dvd_lcm_right x y)) ⟩

theorem lcm_mul_gcd_of_mult (f : Nat.ArithmeticFunction ℝ) (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) 
  (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) : 
    f x * f y = f (x.lcm y) * f (x.gcd y) := by
  have hgcd_ne_zero : x.gcd y ≠ 0 := Nat.gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y ≠ 0 := Nat.lcm_ne_zero hx hy
  have hfi_zero : ∀ {i},  f (i ^ 0) = 1
  · intro i; rw [pow_zero, h_mult.1]
  iterate 4 rw [Nat.ArithmeticFunction.IsMultiplicative.multiplicative_factorization f h_mult (by assumption)]
  iterate 4 rw [Finsupp.prod_of_support_subset _ (s := ((Nat.factorization x).support ⊔ (Nat.factorization y).support)) 
    _ _ (fun _ _ => hfi_zero)]
  · rw [←Finset.prod_mul_distrib, ←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp 
    clear hgcd_ne_zero hlcm_ne_zero hfi_zero
    wlog h : (Nat.factorization x) p ≤ (Nat.factorization y) p
    rw [Nat.lcm_comm, Nat.gcd_comm, mul_comm]
    rw [sup_comm] at hp
    push_neg at h
    apply this f h_mult y x hy hx p hp (le_of_lt h)
    rw [Nat.factorization_lcm hx hy, Nat.factorization_gcd hx hy, Finsupp.inf_apply, Finsupp.sup_apply,
        sup_of_le_right h, inf_of_le_left h, mul_comm]
  · rw [Nat.factorization_gcd hx hy, Nat.support_factorization, Finsupp.support_inf, Finset.sup_eq_union]
    apply Finset.inter_subset_union
  · rw [Nat.factorization_lcm hx hy, Finsupp.support_sup, Finset.sup_eq_union]
  · apply Finset.subset_union_right
  · apply Finset.subset_union_left

theorem mult_lcm_eq_of_ne_zero (f : Nat.ArithmeticFunction ℝ) (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) : 
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [lcm_mul_gcd_of_mult f h_mult x y hx hy]
  rw [mul_div_assoc, div_self, mul_one]
  exact hf

theorem prod_id [CommMonoid R] (s : Finset R) : ∏ n in s, n = s.prod id := rfl

theorem eq_prod_set_factors_of_squarefree {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, p = l :=
  by
  erw [←Finset.prod_val l.factors.toFinset]
  suffices l.factors.toFinset.val = l.factors 
    by rw [this]; rw [Multiset.coe_prod]; exact Nat.prod_factors (Squarefree.ne_zero hl)
  ext p
  rw [List.toFinset_val]
  rw [Multiset.coe_count]; rw [Multiset.coe_count]
  rw [List.count_dedup]
  rw [eq_comm]
  apply List.count_eq_of_nodup
  apply (Nat.squarefree_iff_nodup_factors _).mp hl
  exact Squarefree.ne_zero hl

theorem prod_subset_factors_of_mult (f : Nat.ArithmeticFunction ℝ) 
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
  rw [prod_subset_factors_of_mult f h_mult l.factors.toFinset Finset.Subset.rfl, 
    eq_prod_set_factors_of_squarefree hl]

theorem prod_add_mult (f :Nat.ArithmeticFunction ℝ) (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, (1 + f p) = ∑ d in l.divisors, f d :=
  by
  conv => {lhs; congr; {skip}; ext p; rw [add_comm]}
  rw [Finset.prod_add]
  simp_rw [Finset.prod_eq_one fun _ _ => rfl, mul_one]
  have : l.divisors.filter Squarefree = l.divisors :=
    by
    ext x; constructor
    apply Finset.filter_subset
    intro hx; simp only [Finset.mem_filter]; constructor
    exact hx; rw [Nat.mem_divisors] at hx ; exact Squarefree.squarefree_of_dvd hx.left hl
  rw [←this]
  rw [Nat.sum_divisors_filter_squarefree]
  simp_rw [Nat.factors_eq]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_powerset] at ht 
  rw [Finset.prod_val]
  exact prod_subset_factors_of_mult f h_mult t ht
  exact Squarefree.ne_zero hl

theorem prod_eq_moebius_sum (f : Nat.ArithmeticFunction ℝ) (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, (1 - f p) = ∑ d in l.divisors, μ d * f d :=
  by
  suffices
    ∏ p in l.factors.toFinset, ((1 : ℝ) + (fun x : ℕ => (μ x : ℝ) * f x) p) =
      ∑ d in l.divisors, μ d * f d
    by
    rw [← this]
    apply Finset.prod_congr rfl; intro p hp
    rw [List.mem_toFinset] at hp 
    have hp_prime : p.Prime := by apply Nat.prime_of_mem_factors hp
    
    suffices 1 - f p = 1 + ↑(μ p) * f p 
      by exact this
    rw [Nat.ArithmeticFunction.moebius_apply_prime hp_prime] ; push_cast ; ring 

  apply prod_add_mult (f:=  Nat.ArithmeticFunction.pmul μ f)
  constructor
  suffices (μ 1 : ℝ) * f 1 = 1 
    by exact this
  rw [Nat.ArithmeticFunction.moebius_apply_one]
  rw [h_mult.left]; push_cast ; ring
  intro a b hab
  suffices (μ (a * b) : ℝ) * f (a * b) = μ a * f a * (μ b * f b)
    by exact this
  rw [Nat.ArithmeticFunction.isMultiplicative_moebius.right hab]
  rw [Nat.ArithmeticFunction.IsMultiplicative.map_mul_of_coprime h_mult hab]; push_cast ; ring
  exact hl

end Aux