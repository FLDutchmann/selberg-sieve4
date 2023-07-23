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

theorem id : CompletelyMultiplicative Nat.ArithmeticFunction.id := by
    constructor <;> simp

theorem pmul (f g : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (hg : CompletelyMultiplicative g) : 
    CompletelyMultiplicative (Nat.ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : Nat.ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) (hg : CompletelyMultiplicative g) : 
    CompletelyMultiplicative (Nat.ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : Nat.ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) : 
    Nat.ArithmeticFunction.IsMultiplicative f := 
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with 
  | zero => simp_rw [Nat.zero_eq, pow_zero, hf.1] 
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]

end CompletelyMultiplicative

theorem tmp (M : ℕ) (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) 
  (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ)  (hd : Squarefree d)  (hf_size : ∀n, n.Prime → n ∣ d → f n < 1): 
    f d * ∏ p in d.factors.toFinset, 1 / (1 - f p) 
    ≥ ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p in d.factors.toFinset, 1 / (1 - f p) 
    = ∏ p in d.factors.toFinset, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.ArithmeticFunction.eq_prod_set_factors_of_squarefree hd] }
        rw [←prod_subset_factors_of_mult f hf.isMultiplicative d _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw[one_div, div_eq_mul_inv] 
  _ ≥ ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, (f p)^n  := by
    gcongr with p hp
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [List.mem_toFinset, Nat.mem_factors hd.ne_zero] at hp
    rw [←Nat.Ico_succ_right, geom_sum_Ico, ←mul_div_mul_left (c:= (-1:ℝ)) (f p ^ Nat.succ M - f p ^ 1)]
    gcongr
    · apply hf_nonneg
    · linarith [hf_size p hp.1 hp.2]
    · rw [pow_one]
      have : 0 ≤ f p ^ (M.succ)
      · apply pow_nonneg
        apply hf_nonneg
      linarith only [this]
    · linarith only
    · norm_num
    · apply ne_of_lt $ hf_size p hp.1 hp.2
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)
    
  _ = ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]
-- tactic conv? is good
-- here's the painful part

-- consider divisors_filter_squarefree 
theorem tmp' (M : ℕ) (hM : M ≠ 0) (f : Nat.ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d): 
    ∏ p in d.factors.toFinset, ∑ n in Finset.Icc 1 M, f (p^n)
    = ∑ m in (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M) → ℕ :=
    fun a ha => ∏ p in d.factors.toFinset.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ (a:_) (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M),
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.factors.toFinset then a p hp else 0
  · intro a ha p
    by_cases hp : p ∈ d.factors.toFinset
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply, 
        Nat.Prime.factorization_self (Nat.prime_of_mem_factors $ List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]; push_neg
        exact fun _ => hq
        exact Nat.prime_of_mem_factors $ List.mem_toFinset.mp q.2
        exact (Nat.prime_of_mem_factors $ List.mem_toFinset.mp hp).ne_one
      · intro h
        simp at h
      · exact fun q a_1 => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_factors (List.mem_toFinset.mp q.2)))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_non_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨q, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [List.mem_toFinset, Nat.mem_factors]
      constructor
      · exact hpp
      trans q.1
      apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      apply Nat.dvd_of_mem_factors $ List.mem_toFinset.mp q.2
      exact hd.ne_zero

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M), 
      i a ha ≠ 0
  · intro a ha
    dsimp only
    erw [Finset.prod_ne_zero_iff]
    exact fun p a_1 => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_factors (List.mem_toFinset.mp p.property)))

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
  · intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_factors (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp $ Nat.prime_of_mem_factors (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.eq hc)

  save
  have i_inj : ∀(a b : _) (ha : a ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M)
   (hb : b ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M), i a ha = i b hb → a = b
  · intro a b ha hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := FunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp
  
  save
  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, b = i a ha
  · intro b hb
    have h : (fun p x => (Nat.factorization b) p) ∈ Finset.pi (List.toFinset (Nat.factors d)) fun p => Finset.Icc 1 M
    · rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      rw [List.mem_toFinset] at hp
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt $ Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_factors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_factors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1
        · apply Nat.Squarefree.factorization_le_one p hd
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · exact ne_of_gt $ Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    · apply hi_ne_zero _ h

    intro p
    rw [hfact_i (fun p x => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.factors.toFinset
    · rw [dif_pos hp]
    · rw [dif_neg hp, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [List.mem_toFinset, Nat.mem_factors] at hp
      left
      push_neg at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push_neg
        apply Nat.Prime.dvd_of_dvd_pow hpp (Trans.trans h hb.1.1)
      · left; exact hpp
      refine ne_zero_pow hM hb.1.2


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

lemma Nat.squarefree_dvd_pow (a b N: ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [UniqueFactorizationMonoid.dvd_pow_iff_dvd_of_squarefree ha hN] at hab
  exact hab

example (a b : ℕ) (hab : a ∣ b) (hba : b ∣ a) : a = b := by exact Nat.dvd_antisymm hab hba

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) 
  (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1): 
    s.selbergBoundingSum ≥ ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), s.nu m / m := by
  calc ∑ l in s.prodPrimes.divisors, (if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) 
     ≥ ∑ l in s.prodPrimes.divisors.filter (fun (l:ℕ) => (l:ℝ)^2 ≤ s.level), 
        ∑ m in (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nuDivSelf m        := ?_
   _ ≥ ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), s.nu m / m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p in l.factors.toFinset, ∑ n in Finset.Icc 1 (Nat.floor s.level), s.nu (p^n) / p^n)
    simp_rw [←s.nuDivSelf_apply]
    rw [tmp' (Nat.floor s.level) _ s.nuDivSelf]
    · exact hnu
    · exact hlsq
    · rw [ne_eq, Nat.floor_eq_zero, not_lt]
      exact s.one_le_level
    rw [s.selbergTerms_apply l]
    simp_rw [←s.nuDivSelf_apply]
    apply tmp _ _ hnu _ _ hlsq 
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg

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
    rw [←s.nuDivSelf_apply]
    apply (hnu_nonneg _) 
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
    
theorem primeSieve_boundingSum_ge_sum (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).selbergBoundingSum ≥ ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt y), 1 / (m:ℝ) := by
  trans ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt y), Nat.ArithmeticFunction.zeta m / m
  apply selbergBoundingSum_ge_sum_div
  · intro p hpp hple
    erw [prime_dvd_primorial_iff]
    apply Nat.le_floor
    exact hple
    exact hpp
  · exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
  · intro n; rw [Sieve.nuDivSelf_apply]
    apply div_nonneg
    unfold primeSieve; simp
    by_cases h : n = 0
    · rw [if_pos h]
    · rw [if_neg h]; linarith
    · norm_num
  · intro p hpp hpdvd
    rw [Sieve.nuDivSelf_apply]
    unfold primeSieve; simp
    rw [if_neg, one_div]
    apply inv_lt_one; norm_cast
    exact hpp.one_lt
    exact hpp.ne_zero
  apply le_of_eq
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  rw [Nat.ArithmeticFunction.zeta_apply_ne]; norm_cast
  linarith

theorem primeSieve_boundingSum_ge (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).selbergBoundingSum ≥ Real.log  y / 2 := by
  trans (∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt y), 1 / (m:ℝ))
  · exact primeSieve_boundingSum_ge_sum N y hy
  trans (Real.log $ Real.sqrt y)
  rw [ge_iff_le]
  apply Aux.log_le_sum_one_div (Real.sqrt y)
  rw [Real.le_sqrt] <;> linarith
  apply ge_of_eq
  refine Real.log_sqrt ?h.hx 
  linarith

theorem card_range_filter_dvd (N d : ℕ) (hd : d ≠ 0):
    ((Finset.range N).filter (d ∣ ·)).card = Nat.ceil (N/d:ℝ) := by
  --conv => {rhs; rw [←Finset.card_range (N/d+1)]}
  let f : (i : ℕ) → i < (Nat.ceil (N/d:ℝ)) → ℕ := fun i hi => d*i
  apply Finset.card_eq_of_bijective f
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    use k/d
    constructor
    · simp
      refine Nat.mul_div_cancel' hk.2
    rw [Nat.lt_ceil]
    rw [Nat.cast_div hk.2]
    apply (div_lt_div_right ..).mpr
    norm_cast; exact hk.1
    norm_num 
    rw [Nat.pos_iff_ne_zero]; exact hd
    norm_cast;
  · intro k hk
    dsimp only
    rw [Finset.mem_filter, Finset.mem_range]
    rw [Nat.lt_ceil, lt_div_iff, mul_comm] at hk
    norm_cast at hk
    exact ⟨hk, dvd_mul_right ..⟩
    norm_cast
    apply Nat.pos_of_ne_zero hd
  · exact fun _ _ _ _ hij => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) hij

  /-
  let f : (k : ℕ) → k ∈ ((Finset.range (N/d+1))) → ℕ := fun k hk => d*k
  apply symm
  apply Finset.card_congr f
  · intro a ha
    dsimp only []
    rw [Finset.mem_filter, Finset.mem_range] at *
    constructor
    · apply Nat.lt_mul_of_div_lt ha
-/

theorem primeSieve_multSum_eq (N : ℕ) (y:ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0): 
    (primeSieve N y hy).multSum d = Nat.ceil ((N+1)/d:ℝ) := by
  unfold primeSieve
  simp only [Sieve.multSum, Nat.isUnit_iff, Finset.sum_boole, Finset.mem_range, Nat.cast_inj]
  conv => {rhs; rw[←Nat.cast_one, ←Nat.cast_add]}
  apply card_range_filter_dvd 
  exact hd
  

theorem primeSieve_rem_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d:ℕ) (hd : d ≠ 0):
    (primeSieve N y hy).rem d = Nat.ceil ((N+1)/d:ℝ) - N/d := by
  unfold Sieve.rem
  rw [primeSieve_multSum_eq (hd:=hd)]
  unfold primeSieve
  simp
  rw [if_neg hd]
  ring

theorem primeSieve_abs_rem_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d:ℕ) (hd : d ≠ 0):
    |(primeSieve N y hy).rem d| ≤ 2 := by
  rw [primeSieve_rem_eq (hd:=hd), abs_le]
  constructor
  · apply le_sub_right_of_add_le
    trans ((N + 1) / ↑d)
    · rw [add_comm, add_div]
      have : 0 ≤ 1/(d:ℝ)
      · norm_num
      linarith
    apply Nat.le_ceil
  · apply sub_left_le_of_le_add
    trans ↑(Nat.floor ((N+1)/d:ℝ)+1)
    norm_cast; apply Nat.ceil_le_floor_add_one
    trans ((N+1)/d+1:ℝ)
    · push_cast
      apply add_le_add_right
      apply Nat.floor_le
      apply div_nonneg
      · norm_cast; norm_num
      · norm_num
    have : 1/(d:ℝ) ≤ 1
    · rw [one_div]
      apply inv_le_one; 
      norm_cast
      linarith [Nat.pos_of_ne_zero hd]
    rw [add_div]
    linarith

open Nat.ArithmeticFunction

theorem primeSieve_rem_sum_le (N : ℕ) (y : ℝ) (hy : 1 ≤ y):
    ∑ d in (primeSieve N y hy).prodPrimes.divisors, (if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |(primeSieve N y hy).rem d| else 0) 
      ≤ 2 * y * (1+Real.log y)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d in  Finset.filter (fun d:ℕ => ↑d ≤ y) ((primeSieve N y hy).toSieve.prodPrimes.divisors),  3 ^ ω d * 2 )
  · gcongr with d hd
    · norm_cast
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact primeSieve_abs_rem_eq _ _ _ _ (ne_zero_of_dvd_ne_zero (Sieve.prodPrimes_ne_zero _) hd.1.1)
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  simp_rw [Nat.cast_pow]; push_cast
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := hy) 
  apply Sieve.prodPrimes_squarefree

theorem pi_le_of_y (N : ℕ) (y : ℝ) (hy_lt : 1 < y) :
    π N ≤ 2 * N / Real.log y + 3 * y * (1+Real.log y)^3 := by
  have hy : 1 ≤ y := le_of_lt hy_lt
  trans ((primeSieve N y hy).siftedSum + y)
  · apply pi_le_siftedSum
  suffices Sieve.siftedSum (primeSieve N y hy).toSieve ≤ 2 * N / Real.log y + 2 * y * (1+Real.log y)^3 by
    push_cast at *
    have : y*(1:ℝ) ≤ y*(1+Real.log y)^3
    · gcongr
      refine one_le_pow_of_one_le ?_ 3
      linarith [Real.log_nonneg hy]
    rw [mul_one] at this
    linarith
  trans ((primeSieve N y hy).totalMass / (primeSieve N y hy).selbergBoundingSum) + 
     ∑ d in (primeSieve N y hy).prodPrimes.divisors, (if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |(primeSieve N y hy).rem d| else 0) 
  · apply (SelbergSieve.selberg_bound_simple)
  gcongr (?_ + ?_)
  · trans (N / (Real.log y / 2))
    · gcongr (?_ / ?_)
      · linarith [Real.log_pos hy_lt]
      · rfl
      rw [←ge_iff_le]
      apply primeSieve_boundingSum_ge
    rw [div_eq_mul_inv, inv_div, ←mul_div_assoc, mul_comm]
    push_cast
    rfl
  · apply primeSieve_rem_sum_le
  
#check Aux.sum_one_div_le_log

end PrimeUpperBound
end