/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import SelbergSieve.PrimeCountingUpperBound
import SelbergSieve.ForMathlib.InfiniteSum

open PrimeUpperBound Nat.ArithmeticFunction

open scoped BigOperators 

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

theorem prod_factors_one_div_compMult_ge (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) 
   (d : ℕ) (hd : Squarefree d)  (hf_nonneg : ∀ p, p.Prime → p ∣ d → 0 ≤ f p) (hf_size : ∀ p, p.Prime → p ∣ d → f p < 1): 
    f d * ∏ p in d.factors.toFinset, 1 / (1 - f p) 
    = ∏ p in d.factors.toFinset, ∑' n : ℕ, f (p^(n+1)) := by
  simp_rw[←inv_eq_one_div]
  trans (f d * ∏ p in d.factors.toFinset, ∑' (n : ℕ), f p ^ n)
  · congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [List.mem_toFinset, Nat.mem_factors hd.ne_zero] at hp
    exact symm (tsum_geometric_of_lt_1 (hf_nonneg p hp.1 hp.2) (hf_size p hp.1 hp.2))
  conv => { lhs; congr; rw [←Nat.prod_factors_toFinset_of_squarefree hd] }
  rw [hf.isMultiplicative.map_prod_of_subset_factors _ _ subset_rfl,
    ←Finset.prod_mul_distrib]
  congr; ext p
  rw [←tsum_mul_left]
  congr; ext n
  rw [hf.apply_pow, pow_succ] 

def rad (n : ℕ) : ℕ := if n = 0 then 0 else ∏ p in n.factors.toFinset, p

@[simp]
theorem rad_zero : rad 0 = 0 := if_pos rfl

theorem rad_ext (m n : ℕ) (hm : m ≠ 0) (hn : Squarefree n) : rad m = n ↔ m.factors.toFinset = n.factors.toFinset := by
  unfold rad
  rw [if_neg hm]
  constructor
  · intro h
    ext p
    --simp_rw [List.mem_toFinset, Nat.mem_factors hm, Nat.mem_factors hn.ne_zero]
    rw [←h]
    constructor
    · intro hm -- ⟨hp, hm⟩
      --refine ⟨hp, ?_⟩
      sorry
    repeat sorry
  sorry

theorem test' (p : ℕ) (hp : p.Prime) : p.factorization p = 1 := by 
  exact Nat.Prime.factorization_self hp
  

-- Note this equivalence sends e ↦ ∏ p ^ (e p + 1)
def Equiv.rad_eq (n : ℕ) (hn : n ≠ 0): (n.factors.toFinset → ℕ) ≃ { m : ℕ // m.factors.toFinset = n.factors.toFinset } where
    toFun := fun e ↦ ⟨∏ p in n.factors.toFinset.attach, p.1 ^ (e p + 1), by 
      ext p
      rw [List.mem_toFinset, List.mem_toFinset, Nat.mem_factors hn, Nat.mem_factors]
      · simp only [Nat.isUnit_iff, and_congr_right_iff]
        intro hp
        rw [hp.prime.dvd_finset_prod_iff]
        constructor
        · exact fun ⟨⟨q, hq⟩, _, hpq⟩ ↦ (hp.dvd_of_dvd_pow hpq).trans (Nat.dvd_of_mem_factorization hq)
        · intro hpn
          use! p
          · rw [List.mem_toFinset, Nat.mem_factors hn]
            exact ⟨hp, hpn⟩
          simp_rw [Finset.mem_attach, true_and]
          apply dvd_pow (by rfl) (by norm_num)
      rw [Finset.prod_ne_zero_iff]
      intro ⟨q, hq⟩ _
      simp only [ne_eq, add_pos_iff, or_true, pow_eq_zero_iff]
      exact ne_of_gt (Nat.pos_of_mem_factorization hq)
    ⟩

    invFun := fun ⟨m, hm⟩ ↦ fun p ↦ m.factorization p - 1
    
    left_inv := by
      intro e
      ext ⟨p, hp⟩
      simp only [ge_iff_le]
      rw [Nat.factorization_prod]
      simp only [Nat.factorization_pow, ge_iff_le, Finset.sum_apply', Finsupp.smul_apply]
      rw [Finset.sum_eq_single ⟨p, hp⟩]
      · rw [(Nat.prime_of_mem_factorization hp).factorization_self]
        simp only [smul_eq_mul, mul_one, ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
      · intro ⟨q, hq⟩ _ 
        contrapose!
        simp
        --simp at hpq ⊢ 

        sorry
      repeat sorry

    right_inv := sorry

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d): 
    ∏ p in d.factors.toFinset, ∑' n : ℕ, f (p^(n+1))
    = ∑' m : ℕ, if rad m = n then f m else 0 := by
  rw [prod_tsum_of_summable_norm]
  repeat sorry