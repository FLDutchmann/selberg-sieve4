/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.Primorial
import SelbergSieve.Selberg

set_option autoImplicit false
open scoped Nat Nat.ArithmeticFunction BigOperators Classical

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
example (a:ℕ) : (0*a)
theorem zeta_lt_self_of_prime : ∀ (p : ℕ), Nat.Prime p → (↑ζ:Nat.ArithmeticFunction ℝ) p < (p:ℝ) := by
  intro p hp
  rw [Nat.ArithmeticFunction.natCoe_apply, Nat.ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num;
  exact Nat.succ_le.mp (Nat.Prime.two_le hp)

def primeSieve (N : ℕ) (y : ℝ) (hy : 1 ≤ y): SelbergSieve := {
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

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    let h' : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h
    cases' h' with q hq
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ.mpr h, hp⟩  

theorem primeSieve_siftedSum_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).siftedSum = ((Finset.Icc 1 N).filter (fun d => ∀ p:ℕ, p.Prime → p ≤ y → ¬p ∣ d)).card := by
  dsimp only [Sieve.siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr;
  ext d; constructor
  · intro hd
    rw [Finset.mem_filter] at *
    constructor
    · exact hd.1
    · intro p hpp hpy
      rw [←Nat.Prime.coprime_iff_not_dvd hpp]
      apply Nat.coprime.coprime_dvd_left _ hd.2
      unfold primeSieve
      rw [prime_dvd_primorial_iff _ _ hpp]
      apply Nat.le_floor hpy
  · intro h
    rw [Finset.mem_filter]
    sorry
  sorry

theorem pi_le_siftedSum (N : ℕ) (y : ℝ) (hy : 1 ≤ y) : 
    π N ≤ (primeSieve N y hy).siftedSum + y := by
  rw [primeSieve_siftedSum_eq]
  sorry

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
    ≥ ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n) / p^n := by
  simp_rw [one_div]
  sorry

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
  
theorem Nat.factorization_le_self (m p: ℕ) : m.factorization p ≤ m := by
  rw [← @Nat.factors_count_eq]
  trans (m.factors.length)
  exact List.count_le_length p (Nat.factors m)
  apply?

example (a b : ℕ) (hab : a ∣ b) (hba : b ∣ a) : a = b := by exact Nat.dvd_antisymm hab hba

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) 
  (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n): 
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
    have hprod_pos : 0 < (∏ p in List.toFinset (Nat.factors m), p)
    · apply Finset.prod_pos; 
      intro p hp; exact Nat.pos_of_mem_factors $ List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p in List.toFinset (Nat.factors m), p) ^ ⌊s.level⌋₊ ≠ 0
    · apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    have hm_ne_zero : m ≠ 0
    · exact ne_of_gt $ Nat.succ_le.mp hm.1
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
    · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
      trans (m:ℝ)
      · norm_cast; apply Nat.le_of_dvd (Nat.succ_le.mp hm.1)
        apply Nat.prod_prime_factors_dvd
      exact hm.2
      apply le_of_lt; norm_cast;
    constructor; constructor 
    · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
      intro p
      have hy_mul_prod_nonneg : 0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p in List.toFinset (Nat.factors m), p)) p
      · apply mul_nonneg; apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]; norm_num
      trans (Nat.factorization m) p * 1
      · rw [mul_one]; 
      trans ⌊s.level⌋₊ * Nat.factorization (∏ p in List.toFinset (Nat.factors m), p) p
      swap
      · apply le_rfl
      by_cases hpp : p.Prime
      swap; 
      · rw [Nat.factorization_eq_zero_of_non_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
      by_cases hpdvd : p ∣ m
      swap
      · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
      apply mul_le_mul
      trans m
      · apply le_of_lt $ Nat.factorization_lt _ _
        apply hm_ne_zero
      apply Nat.le_floor
      refine le_trans hm.2 ?_
      apply sqrt_le_self _ s.one_le_level
      rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp $ ne_of_gt hprod_pos, pow_one]
      apply Finset.dvd_prod_of_mem
      rw [List.mem_toFinset, Nat.mem_factors]
      exact ⟨hpp, hpdvd⟩
      exact hm_ne_zero
      norm_num
      norm_num
      exact hm_ne_zero
    · exact hprod_ne_zero
    · apply Nat.prod_prime_factors_dvd
    · apply Real.sqrt_nonneg
  · intro i _ _
    apply div_nonneg (hnu_nonneg _) 
    norm_num
  · intro i hi j hj hij
    intro s hsi hsj 
    intro x hx; 
    simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
    specialize hsi hx
    specialize hsj hx
    simp_rw [Finset.mem_filter, Nat.mem_divisors] at *
    sorry
    

end PrimeUpperBound
end