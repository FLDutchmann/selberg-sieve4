/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
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

theorem zeta_lt_self_of_prime : ∀ (p : ℕ), Nat.Prime p → (↑ζ:Nat.ArithmeticFunction ℝ) p < (p:ℝ) := by
  intro p hp
  rw [Nat.ArithmeticFunction.natCoe_apply, Nat.ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num;
  exact Nat.succ_le.mp (Nat.Prime.two_le hp)

def primeSieve (N : ℕ) (y : ℝ) (hy : 1 ≤ y): SelbergSieve := {
  support := Finset.range (N + 1)
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
    (primeSieve N y hy).siftedSum = ((Finset.range (N + 1)).filter (fun d => ∀ p:ℕ, p.Prime → p ≤ y → ¬p ∣ d)).card := by
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
    rw [Finset.mem_filter] at *
    constructor
    · exact h.1
    refine Nat.coprime_of_dvd ?_
    intro p hp
    erw [prime_dvd_primorial_iff _ _ hp]
    intro hpy
    apply h.2 p hp
    trans ↑(Nat.floor y)
    · norm_cast
    · apply Nat.floor_le
      linarith only [hy]
  simp_rw [Nat.cast_one]
  exact fun _ _ => rfl

theorem prime_subset (N : ℕ) (y : ℝ) :
    (Finset.range (N + 1)).filter Nat.Prime ⊆ ((Finset.range (N + 1)).filter (fun d => ∀ p:ℕ, p.Prime → p ≤ y → ¬p ∣ d)) 
      ∪ Finset.Icc 1 (Nat.floor y) := by
  intro p
  simp_rw [Finset.mem_union, Finset.mem_filter]
  intro h
  by_cases hp_le : p ≤ y
  · right; 
    rw [Finset.mem_Icc]
    exact ⟨le_of_lt h.2.one_lt, Nat.le_floor hp_le⟩
  constructor; constructor
  · exact h.1
  · intro q hq hq'
    rw [prime_dvd_prime_iff_eq hq.prime h.2.prime]
    intro hqp
    rw [hqp] at hq'
    linarith only [hp_le, hq']


theorem pi_le_siftedSum (N : ℕ) (y : ℝ) (hy : 1 ≤ y) : 
    π N ≤ (primeSieve N y hy).siftedSum + y := by
  trans ((primeSieve N y hy).siftedSum + Nat.floor y)
  · have : (Finset.Icc 1 (Nat.floor y)).card = Nat.floor y 
    · rw [Nat.card_Icc]; norm_num
    rw [primeSieve_siftedSum_eq, ←this]
    unfold Nat.primeCounting
    unfold Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range]
    norm_cast
    trans (((Finset.range (N + 1)).filter (fun d => ∀ p:ℕ, p.Prime → p ≤ y → ¬p ∣ d)) 
      ∪ Finset.Icc 1 (Nat.floor y)).card
    · exact Finset.card_le_of_subset (prime_subset N y)
    apply Finset.card_union_le
  · gcongr
    apply Nat.floor_le 
    linarith only [hy]

def CompletelyMultiplicative (f : Nat.ArithmeticFunction ℝ) : Prop := f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

namespace CompletelyMultiplicative
open Nat.ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
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

theorem pmul (f g : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (hg : CompletelyMultiplicative g) : 
    CompletelyMultiplicative (Nat.ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv (f g : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (hg : CompletelyMultiplicative g) : 
    CompletelyMultiplicative (Nat.ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) : 
    Nat.ArithmeticFunction.IsMultiplicative f := 
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with 
  | zero => simp_rw [Nat.zero_eq, pow_zero, hf.1] 
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]

end CompletelyMultiplicative

theorem tmp (M : ℕ) (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (hf_size : ∀n, f n < 1) 
  (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ)  (hd : Squarefree d) : 
    f d * ∏ p in d.factors.toFinset, 1 / (1 - f p) 
    ≥ ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p in d.factors.toFinset, 1 / (1 - f p) 
    = ∏ p in d.factors.toFinset, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.ArithmeticFunction.eq_prod_set_factors_of_squarefree hd] }
        rw [←prod_subset_factors_of_mult f hf.isMultiplicative d _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw[one_div, div_eq_mul_inv] 
  _ ≥ ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, (f p)^n  := by
    gcongr with p _
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [←Nat.Ico_succ_right, geom_sum_Ico, ←mul_div_mul_left (c:= (-1:ℝ)) (f p ^ Nat.succ M - f p ^ 1)]
    gcongr
    · apply hf_nonneg
    · linarith [hf_size p]
    · rw [pow_one]
      have : 0 ≤ f p ^ (M.succ)
      · apply pow_nonneg
        apply hf_nonneg
      linarith only [this]
    · linarith only
    · norm_num
    · apply ne_of_lt $ hf_size p
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)
  _ = ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]
-- tactic conv? is good
-- here's the painful part

-- consider divisors_filter_squarefree 
theorem tmp' (M : ℕ) (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d): 
    ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n)
    = ∑ m in (d^M).divisors.filter (d ∣ ·), f m := by
  
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M) → ℕ :=
    fun a ha => ∏ p in d.factors.toFinset.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ (a:_) (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M),
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.factors.toFinset then a p hp else 0
  · intro a ha p
    by_cases hp : p ∈ d.factors.toFinset
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply, 
        Nat.Prime.factorization_self (Nat.prime_of_mem_factors $ List.mem_toFinset.mp hp)]
      · ring
      · sorry
      repeat sorry
    repeat sorry

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M), 
      i a ha ≠ 0
  · sorry 

  have hi_factors : ∀ a ha, (i a ha).factors.toFinset = d.factors.toFinset
  · intro a ha
    ext p; simp_rw[List.mem_toFinset, Nat.mem_factors hd.ne_zero, Nat.mem_factors (hi_ne_zero a ha)]
    constructor
    · intro h
      

    


  save
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M), 
      i a ha ∈ (d^M).divisors.filter (d ∣ ·)
  · intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero (hi_ne_zero a ha), 
      ←Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _; 
      rw [hfact_i a ha]
      by_cases hp :  p ∈ List.toFinset (Nat.factors d)
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num;
          exact (ha p hp).2
        · gcongr
          rw [List.mem_toFinset, Nat.mem_factors hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact Nat.Squarefree.factorization_le_one p hd
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  save
  have h : ∀ (a : _) (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M), 
      ∏ p in d.factors.toFinset.attach, f (p.1 ^ (a p p.2)) = f (i a ha)
  · sorry
  save
  have i_inj : ∀(a b : _) (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M)
   (hb : b ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M), i a ha = i b hb → a = b
  · sorry
  save
  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, b = i a ha
  · sorry

  exact Finset.sum_bij i hi h i_inj i_surj

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
  sorry
  --apply?

lemma Nat.squarefree_dvd_pow (a b N: ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [UniqueFactorizationMonoid.dvd_pow_iff_dvd_of_squarefree ha hN] at hab
  exact hab

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
    rw [tmp']
    · exact hnu
    · exact hlsq
    rw [Sieve.selbergTerms_apply]
    sorry
    -- apply tmp _ _ _ _ _ _ hlsq
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
    intro t hti htj 
    intro x hx; 
    simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j
    · intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (s.squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j
    · apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i
    · apply h j i hj.1.1 htj.2 hti.1.1
    exact hij $ Nat.dvd_antisymm hidvdj hjdvdi
    

end PrimeUpperBound
end