/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.Primorial
import SelbergSieve.Selberg

set_option autoImplicit false
open scoped Nat Nat.ArithmeticFunction BigOperators

noncomputable section
namespace PrimeUpperBound

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/-
  https://leanprover-community.github.io/mathlib_docs/analysis/inner_product_space/basic.html#real_inner_le_norm
  https://leanprover-community.github.io/mathlib_docs/analysis/inner_product_space/pi_L2.html#orthonormal_basis.sum_inner_mul_inner
-/
example (a b c : ℕ) (h : a * b ∣ a * c) (h' : a ≠ 0) : b ∣ c := by exact Iff.mp (mul_dvd_mul_iff_left h') h

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) : 
    Squarefree (∏ p in s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)] at h_dvd
    cases' Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h_dvd with q hq
    rw [Finset.mem_erase] at hq
    exact hq.1.1 $ symm $ (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p in s, p := Trans.trans (dvd_mul_right p p) h_dvd 
    cases' Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) this with q hq
    have heq : p = q
    · rw [←Nat.prime_dvd_prime_iff_eq]; exact hq.2
      exact hp; exact h q hq.1
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter]; 
  exact fun _ h => h.2

theorem zeta_pos_of_prime : ∀ (p : ℕ), Nat.Prime p → (0:ℝ) < (↑ζ:Nat.ArithmeticFunction ℝ) p := by 
  intro p hp
  rw [Nat.ArithmeticFunction.natCoe_apply, Nat.ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime : ∀ (p : ℕ), Nat.Prime p → (↑ζ:Nat.ArithmeticFunction ℝ) p < (p:ℝ) := by
  intro p hp
  rw [Nat.ArithmeticFunction.natCoe_apply, Nat.ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num;
  exact Nat.succ_le.mp (Nat.Prime.two_le hp)

def primeSieve (N : ℕ) (y : ℝ) (hy : 1≤ y): SelbergSieve := {
  support := Finset.Icc 1 N
  prodPrimes := primorial (Nat.floor y)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  ha_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := ζ
  nu_mult := Nat.ArithmeticFunction.IsMultiplicative.nat_cast Nat.ArithmeticFunction.isMultiplicative_zeta
  nu_pos_of_prime := fun p hp _ => zeta_pos_of_prime p hp
  nu_lt_self_of_prime := fun p hp _ => zeta_lt_self_of_prime p hp
  level := y
  one_le_level := hy
}

def CompletelyMultiplicative (f : Nat.ArithmeticFunction ℝ) : Prop := f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

theorem CompletelyMultiplicative_zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  simp_rw [Nat.ArithmeticFunction.natCoe_apply, Nat.ArithmeticFunction.zeta_apply, ite_false, Nat.cast_one,
    mul_eq_zero, Nat.cast_ite, CharP.cast_eq_zero, mul_ite, mul_zero, mul_one, true_and]
  intro a b; 
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [if_neg, if_neg hb, if_neg ha]; ring
  push_neg; exact ⟨ha, hb⟩

theorem tmp (M : ℕ) (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d) : 
    f d / ↑d * ∏ p in d.factors.toFinset, 1 / (1 - f p/p) 
    ≥ ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n) / p^n := sorry

-- here's the painful part
theorem tmp' (M : ℕ) (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d): 
    ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n) / p^n
    = ∑ m in (d^M).divisors.filter (d ∣ ·), f m / m := sorry

theorem lem0 (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime): 
    ∏ p in s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  refine le_self_pow hx ?right.h
  norm_num

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) 
  (hnu : CompletelyMultiplicative s.nu) : 
    s.selbergBoundingSum ≥ ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), s.nu m / m := by
  calc ∑ l in s.prodPrimes.divisors, (if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) 
     ≥ ∑ l in s.prodPrimes.divisors.filter (fun (l:ℕ) => (l:ℝ)^2 ≤ s.level), 
        ∑ m in (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m / m        := ?_
   _ ≥ ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), s.nu m / m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p in l.factors.toFinset, ∑ n in Finset.Icc 1 (Nat.floor s.level), s.nu (p^n) / p^n)
    dsimp [Sieve.selbergTerms]
    rw [tmp']
    · exact hnu
    · exact hlsq
    apply tmp _ _ hnu _ hlsq
  rw [←Finset.sum_biUnion]; apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm;
    have hprod_ne_zero :  (∏ p in List.toFinset (Nat.factors m), p) ^ ⌊s.level⌋₊ ≠ 0
    · sorry
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    use ∏ p in m.factors.toFinset, p
    constructor; constructor; constructor
    · apply lem0 <;> simp_rw [List.mem_toFinset] <;> intro p hp
      · apply hP p $ Nat.prime_of_mem_factors hp 
        trans (m:ℝ)
        · norm_cast; exact Nat.le_of_mem_factors hp
        trans (Real.sqrt s.level)
        · exact hm.2
        apply sqrt_le_self s.level s.one_le_level
      exact Nat.prime_of_mem_factors hp
    · exact s.prodPrimes_ne_zero
    · sorry
    constructor; constructor 
    · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
      sorry
      sorry
    · exact hprod_ne_zero
    · apply Nat.prod_prime_factors_dvd
    · apply Real.sqrt_nonneg
  · intro i _ _
    sorry
  · sorry

end PrimeUpperBound
end