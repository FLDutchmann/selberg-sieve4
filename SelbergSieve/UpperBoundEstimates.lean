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

/- Unneeded? see Nat.Prime.factorization instead -/
theorem Nat.Prime.factorization_eq_zero_of_ne {p n : ℕ} (hp : p.Prime) (hpq : p ≠ n) :
    Nat.factorization p n = 0 := by
  by_cases hn : n = 1
  · rw [hn]; simp
  apply Nat.factorization_eq_zero_of_not_dvd
  rw [hp.dvd_iff_eq hn]
  exact hpq

theorem prodPrimes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree <| ∏ p in s, p := by
  have h : ∀ p ∈ s, p ≠ 0
  · exact fun p hp => (hs p hp).ne_zero
  refine (Nat.squarefree_iff_factorization_le_one <| Finset.prod_ne_zero_iff.mpr h).mpr ?_
  rw [Nat.factorization_prod h]
  intro p
  rw [@Finset.sum_apply']
  by_cases hps : p ∈ s
  · rw [Finset.sum_eq_single p, (hs p hps).factorization_self]
    · intro q hq hqp
      simp [hs q hq, hqp]
    simp only [hps, not_true, IsEmpty.forall_iff]
  · rw[Finset.sum_eq_zero]
    · norm_num
    intro q hq
    simp [hs q hq, ne_of_mem_of_not_mem hq hps]

def rad (n : ℕ) : ℕ := if n = 0 then 0 else ∏ p in n.factors.toFinset, p

@[simp]
theorem rad_zero : rad 0 = 0 := if_pos rfl

@[simp]
theorem rad_apply {n : ℕ} (hn : n ≠ 0) : rad n = ∏ p in n.factors.toFinset, p :=
  if_neg hn

@[simp]
theorem rad_eq_zero_iff (n : ℕ) : rad n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    simp only [ne_eq, hn, rad_apply] at h
    obtain ⟨p, hpn, rfl⟩ := Finset.prod_eq_zero_iff.mp h
    simp[Nat.mem_factors hn] at hpn
  · rintro rfl; simp

theorem rad_squarefree {n : ℕ} (hn : n ≠ 0) : Squarefree <| rad n := by
  rw [rad_apply hn]
  exact prodPrimes_squarefree fun p hp ↦ Nat.prime_of_mem_factorization hp

theorem rad_ext (m n : ℕ) (hn : Squarefree n) : rad m = n ↔ m ≠ 0 ∧ m.factors.toFinset = n.factors.toFinset := by
  unfold rad
  constructor
  · intro h
    by_cases hm : m = 0
    · simp only [hm, ne_eq, Nat.factors_zero, List.toFinset_nil, false_and, Finset.prod_empty, ite_true] at h ⊢
      exact hn.ne_zero h.symm
    refine ⟨hm, ?_⟩
    rw [if_neg hm] at h
    ext p
    simp_rw [List.mem_toFinset, Nat.mem_factors hn.ne_zero, Nat.mem_factors hm]
    simp only [Nat.isUnit_iff, and_congr_right_iff]
    intro hp
    rw [←h, hp.prime.dvd_finset_prod_iff]
    constructor
    · exact fun hpm ↦ ⟨p, List.mem_toFinset.mpr <| (Nat.mem_factors hm).mpr ⟨hp, hpm⟩, dvd_rfl⟩
    · exact fun ⟨q, hq, hpq⟩ ↦ hpq.trans <| Nat.dvd_of_mem_factorization hq
  · intro ⟨hm, hmn⟩
    rw[if_neg hm, hmn]
    exact Nat.prod_factors_toFinset_of_squarefree hn

theorem test' (p : ℕ) (hp : p.Prime) : p.factorization p = 1 := by
  exact Nat.Prime.factorization_self hp

theorem rad_ext' (n m : ℕ) : rad m = rad n ↔ ∀ p, p.Prime → (p ∣ m ↔ p ∣ n) := by
  by_cases hn : n = 0
  · rw[hn]; simp
    constructor
    · rintro rfl; simp
    · contrapose!
      intro h

      sorry
  simp [hn]
  constructor
  · intro h
    sorry
  · intro h
    sorry

example (p q : Type _) : p = q ↔ q = p := by apply?

def Equiv.primeFactors_eq (n : ℕ) (hn : n ≠ 0) : (n.primeFactors → ℕ) ≃ { m : ℕ // m.primeFactors = n.primeFactors} where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
-- Note this equivalence sends e ↦ ∏ p ^ (e p + 1)
def Equiv.rad_eq (n : ℕ) (hn : n ≠ 0): (n.factors.toFinset → ℕ) ≃ { m : ℕ // rad m = rad n } where
    toFun := fun e ↦ ⟨∏ p in n.factors.toFinset.attach, p.1 ^ (e p + 1), by
      rw [rad_ext]
      constructor
      · apply Finset.prod_ne_zero_iff.mpr

        sorry
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
        simp only [ne_eq, Subtype.mk.injEq, smul_eq_mul, mul_eq_zero, add_eq_zero, and_false, false_or]
        intro hqp
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [List.mem_toFinset, Nat.mem_factors hn] at hp hq
        rw [Nat.prime_dvd_prime_iff_eq hp.1 hq.1, eq_comm]
        exact hqp
      · simp only [Finset.mem_attach, not_true, smul_eq_mul, mul_eq_zero, add_eq_zero, and_false, false_or,
        IsEmpty.forall_iff]
      · simp only [Finset.mem_attach, ne_eq, add_pos_iff, or_true, pow_eq_zero_iff, forall_true_left, Subtype.forall,
        List.mem_toFinset]
        exact fun p hp => ne_of_gt (Nat.pos_of_mem_factors hp)

    right_inv := by
      intro ⟨m, hm⟩
      simp only [ge_iff_le, Subtype.mk.injEq]
      trans ∏ x in Finset.attach (List.toFinset (Nat.factors n)), x.1 ^ ((Nat.factorization m) x)
      · congr
        ext ⟨p, hp⟩
        simp only [ge_iff_le]
        congr
        apply Nat.sub_add_cancel
        rw [←Nat.Prime.dvd_iff_one_le_factorization]
        · rw [←hm] at hp
          exact Nat.dvd_of_mem_factorization hp
        · exact Nat.prime_of_mem_factorization hp



theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d):
    ∏ p in d.factors.toFinset, ∑' n : ℕ, f (p^(n+1))
    = ∑' m : ℕ, if rad m = n then f m else 0 := by
  rw [prod_tsum_of_summable_norm]
  repeat sorry
