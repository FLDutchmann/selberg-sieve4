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

def Multiplicative (f : ℕ → ℝ) : Prop :=
  f 1 = 1 ∧ ∀ x y : ℕ, x.coprime y → f (x * y) = f x * f y

/- https://github.com/leanprover-community/mathlib4/pull/5669 -/
theorem coprime_of_mul_squarefree (x y : ℕ) (h : Squarefree <| x * y) : x.coprime y :=
  by
  by_contra h_ncop
  rw [Nat.Prime.not_coprime_iff_dvd] at h_ncop 
  cases' h_ncop with p hp
  rcases hp with ⟨hpp, hpx, hpy⟩
  cases' hpx with r hx
  cases' hpy with s hy
  have : p * p ∣ x * y
  use r * s
  rw [hy]; rw [hx]; ring
  rw [Nat.squarefree_iff_prime_squarefree] at h 
  specialize h p hpp
  exact h this
  
theorem lcm_squarefree_of_squarefree {n m : ℕ} (hn : Squarefree n) (hm : Squarefree m) :
    Squarefree (n.lcm m) := by
  have hn_ne_zero := Squarefree.ne_zero hn
  have hm_ne_zero := Squarefree.ne_zero hm
  have hlcm_ne_zero := Nat.lcm_ne_zero hn_ne_zero hm_ne_zero
  rw [Nat.squarefree_iff_factorization_le_one hn_ne_zero] at hn
  rw [Nat.squarefree_iff_factorization_le_one hm_ne_zero] at hm 
  rw [Nat.squarefree_iff_factorization_le_one hlcm_ne_zero]
  rw [Nat.factorization_lcm hn_ne_zero hm_ne_zero]
  intro p
  rw [Finsupp.sup_apply, sup_le_iff]
  exact ⟨hn p, hm p⟩

lemma temp {α : Type u_1} {M : Type u_8} {N : Type u_10} [Zero M] [CommMonoid N] (f : α →₀ M) (g : α → M → N) :
  Finsupp.prod f g = finprod fun a => g a (f a) := by 
  
  sorry
lemma tmp (a : ℕ) : (Nat.factorization a).support = a.factors.toFinset := rfl

/- Can we do without the Squarefrees? 
  See Nat.ArithmeticFunction.IsMultiplicative.multiplicative_factorization -/
theorem mult_gcd_lcm_of_squarefree (f : ℕ → ℝ) (h_mult : Multiplicative f) (x y : ℕ)
    (hx : Squarefree x) (hy : Squarefree y) : f x * f y = f (x.lcm y) * f (x.gcd y) :=
  by
  /-
    iterate 4 rw[Nat.ArithmeticFunction.IsMultiplicative.multiplicative_factorization f h_mult]
    rw [Finsupp.prod_of_support_subset _ (s := ((Nat.factorization x).support ⊔ (Nat.factorization y).support)) 
      (Finset.subset_union_left _ _), 
      Finsupp.prod_of_support_subset _ (s := ((Nat.factorization x).support ⊔ (Nat.factorization y).support)) 
      (Finset.subset_union_right _ _), 
      Finsupp.prod_of_support_subset _ (s := ((Nat.factorization x).support ⊔ (Nat.factorization y).support)),
      Finsupp.prod_of_support_subset _ (s := ((Nat.factorization x).support ⊔ (Nat.factorization y).support))]
    rw [←Finset.prod_mul_distrib, ←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro p hp
    · sorry
    · --rw [Nat.factorization_gcd]; apply Function.support_inf (f := Nat.factorization)
      simp_rw [Nat.support_factorization]
      rw []-/
  have hgcd : Squarefree (x.gcd y) := 
    by apply Squarefree.squarefree_of_dvd _ hx; exact Nat.gcd_dvd_left x y
  dsimp only [Nat.lcm]
  have hassoc : x * y / x.gcd y = x * (y / x.gcd y) := Nat.mul_div_assoc x (Nat.gcd_dvd_right x y)
  rw [hassoc]
  have hx_cop_yg : x.coprime (y / x.gcd y) :=
    by
    apply coprime_of_mul_squarefree
    rw [← hassoc]; exact lcm_squarefree_of_squarefree hx hy
  rw [h_mult.right x (y / x.gcd y) hx_cop_yg]
  have : (y / x.gcd y).coprime (x.gcd y) :=
    by
    apply coprime_of_mul_squarefree
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_right x y)]
    exact hy
  rw [mul_assoc]
  rw [← h_mult.right _ _ this]
  rw [Nat.div_mul_cancel (Nat.gcd_dvd_right x y)]

theorem mult_lcm_eq_of_ne_zero (f : ℕ → ℝ) (h_mult : Multiplicative f) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) (hx : Squarefree x) (hy : Squarefree y) : 
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [mult_gcd_lcm_of_squarefree f h_mult x y hx hy]
  rw [mul_div_assoc, div_self, mul_one]
  exact hf

theorem eq_prod_set_factors_of_squarefree {l : ℕ} (hl : Squarefree l) :
    l.factors.toFinset.val.prod = l :=
  by
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

theorem prod_subset_factors_of_mult (f : ℕ → ℝ) (h_mult : Multiplicative f) {l : ℕ}
    (hl : Squarefree l) :
    ∀ t : Finset ℕ, t ⊆ l.factors.toFinset → ∏ a : ℕ in t, f a = f t.val.prod :=
  by
  intro t; intro ht; rw [Finset.prod_val t];
  induction' t using Finset.induction_on with p t hpt h_ind 
  --intro h
  simp only [eq_self_iff_true, Finset.prod_empty, Finset.empty_val, Multiset.prod_zero, h_mult.left]
  --intro p t hpt h_ind h_sub
  have ht_sub : t ⊆ l.factors.toFinset := Finset.Subset.trans (Finset.subset_insert p t) ht
  have hl_primes : ∀ a : ℕ, a ∈ l.factors.toFinset → a.Prime :=
    by
    intro a hal
    rw [List.mem_toFinset] at hal 
    exact Nat.prime_of_mem_factors hal
  have ht_primes : ∀ a : ℕ, a ∈ t → a.Prime :=
    by
    intro a ha; apply hl_primes a
    apply Finset.mem_of_subset ht_sub ha
  have hp_prime : p.Prime :=
    by apply hl_primes p; apply Finset.mem_of_subset ht; exact Finset.mem_insert_self p t
  have hp_cop : p.coprime (t.prod _root_.id) :=
    by
    rw [Nat.Prime.coprime_iff_not_dvd hp_prime]
    rw [Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp_prime) _root_.id]
    push_neg; intro a ha; by_contra hpa
    rw [id.def] at hpa 
    have : p = a :=
      eq_comm.mp ((Nat.Prime.dvd_iff_eq (ht_primes a ha) (Nat.Prime.ne_one hp_prime)).mp hpa)
    rw [this] at hpt 
    exact hpt ha
  specialize h_ind ht_sub
  calc
    ∏ a : ℕ in insert p t, f a = f p * ∏ a : ℕ in t, f a := Finset.prod_insert hpt
    _ = f p * f (t.prod _root_.id) := by rw [h_ind]
    _ = f (p * ∏ a in t, a) := by rw [h_mult.right p (∏ a in t, a) hp_cop]; rfl
    _ = f (∏ a in insert p t, a) := by rw [Finset.prod_insert hpt]

theorem prod_factors_of_mult (f : ℕ → ℝ) (h_mult : Multiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a : ℕ in l.factors.toFinset, f a = f l :=
  by
  rw [prod_subset_factors_of_mult f h_mult hl l.factors.toFinset Finset.Subset.rfl]
  suffices : l.factors.toFinset.val.prod = l; rw [this]
  exact eq_prod_set_factors_of_squarefree hl
 
theorem prod_add_mult (f : ℕ → ℝ) (h_mult : Multiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, (1 + f p) = ∑ d in l.divisors, f d :=
  by
  simp_rw [add_comm]
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
  have hfact_eq :
    l.factors.toFinset.powerset =
      (UniqueFactorizationMonoid.normalizedFactors l).toFinset.powerset :=
    by rw [Nat.factors_eq]; simp
  apply Finset.sum_congr hfact_eq
  intro t ht
  rw [← hfact_eq] at ht 
  rw [Finset.mem_powerset] at ht 
  exact prod_subset_factors_of_mult f h_mult hl t ht
  exact Squarefree.ne_zero hl

theorem prod_eq_moebius_sum (f : ℕ → ℝ) (h_mult : Multiplicative f) {l : ℕ} (hl : Squarefree l) :
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

  apply prod_add_mult
  constructor
  suffices (μ 1 : ℝ) * f 1 = 1 
    by exact this
  rw [Nat.ArithmeticFunction.moebius_apply_one]
  rw [h_mult.left]; push_cast ; ring
  intro a b hab
  suffices (μ (a * b) : ℝ) * f (a * b) = μ a * f a * (μ b * f b)
    by exact this
  rw [Nat.ArithmeticFunction.isMultiplicative_moebius.right hab]
  rw [h_mult.right a b hab]; push_cast ; ring
  exact hl

end Aux