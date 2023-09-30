/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
import SelbergSieve.SieveLemmas
import SelbergSieve.AesopDiv

noncomputable section

open scoped BigOperators Classical Sieve

open Finset Real Nat Sieve.UpperBoundSieve Nat.ArithmeticFunction Sieve

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)


structure SelbergSieve extends Sieve where mk ::
  level : ℝ
  one_le_level : 1 ≤ level

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => Sieve.nu (toSieve s)
local notation3 "P" => Sieve.prodPrimes (toSieve s)
local notation3 "a" => Sieve.weights (toSieve s)
local notation3 "X" => Sieve.totalMass (toSieve s)
local notation3 "R" => Sieve.rem (toSieve s)  -- this one seems broken
local notation3 "g" => Sieve.selbergTerms (toSieve s)
local notation3 "y" => SelbergSieve.level s
local notation3 "hy" => SelbergSieve.one_le_level s

--set_option profiler true
@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l in divisors P, if (l : ℝ) ^ 2 ≤ y then g l else 0

local notation3 "S" => SelbergSieve.selbergBoundingSum s

@[aesop safe (rule_sets [Divisibility])] 
theorem selbergBoundingSum_pos :
    0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos; intro l hl
  rw [mem_filter, mem_divisors] at hl
  · apply s.selbergTerms_pos _ (hl.1.1)
  rw [Finset.Nonempty]; use 1
  rw [mem_filter]
  constructor
  · apply one_mem_divisors.mpr s.prodPrimes_ne_zero
  rw [cast_one, one_pow]
  exact s.one_le_level

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    d / ν d * g d * μ d / S *
      ∑ m in divisors P, if (d * m : ℝ) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬(d : ℝ) ^ 2 ≤ y) :
    s.selbergWeights d = 0 := by
  dsimp only [selbergWeights]
  by_cases h : d ∣ P
  swap
  · rw [if_neg h]
  rw [if_pos h, mul_eq_zero_of_right _]; 
  apply Finset.sum_eq_zero; intro m hm
  rw [if_neg]
  by_contra hyp
  push_neg at hd
  have : (d:ℝ)^2 ≤ (m*d:ℝ)^2 := by
    norm_cast; 
    refine Nat.pow_le_pow_of_le_left ?h 2
    exact Nat.le_mul_of_pos_left (Nat.pos_of_mem_divisors hm)
  linarith [hyp.1]

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ s.selbergWeights d * μ d :=
  by
  have := s.selbergBoundingSum_nonneg
  dsimp only [selbergWeights]
  rw [if_pos hdP]; rw [mul_assoc]
  trans ((μ d :ℝ)^2 * (d/ν d) * g d / S * ∑ m in divisors P,
          if (d * m:ℝ) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap; apply le_of_eq; ring
  apply mul_nonneg; apply div_nonneg; apply mul_nonneg; apply mul_nonneg
  · apply sq_nonneg
  · rw [←inv_div, inv_nonneg]
    exact le_of_lt $ s.nu_div_self_pos hdP
  · exact le_of_lt $ s.selbergTerms_pos d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  by_cases h : (↑d * ↑m:ℝ) ^ 2 ≤ y ∧ m.Coprime d
  · rw [if_pos h]; exact le_of_lt $ s.selbergTerms_pos m (dvd_of_mem_divisors hm)
  · rw [if_neg h]

lemma sum_mul_subst (k n: ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) : 
      ∑ l in n.divisors, f l
    = ∑ m in n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · rw [hn]; simp
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · intro m _
      rw [if_neg]  
      revert hkn; contrapose!; intro h
      exact Trans.trans (Nat.dvd_mul_right k m) h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      aesop_div
  trans (∑ l in n.divisors, ∑ m in n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero]; 
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m hmn hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel]; 
      aesop_div
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    by_cases hdvd : k*m ∣ n
    · rw [if_pos hdvd]
      rw [←Aux.sum_intro]
      aesop_div
    · rw [if_neg hdvd] 
      apply sum_eq_zero; intro l hl
      apply if_neg; 
      aesop_div

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d / d * s.selbergWeights d =
      1 / S * μ d *
        ∑ l in divisors P, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g l else 0 :=
  by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]; ring
    intro l hl; rw [mem_divisors] at hl 
    rw [if_neg]; push_neg; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [sum_mul_subst d P]
  apply sum_congr rfl
  intro m hm
  rw [←ite_mul_zero_right, ←ite_and, ←ite_mul_zero_right, ←ite_mul_zero_right]
  apply if_ctx_congr _ _ fun _ => rfl
  · rw [cast_mul, coprime_comm]
    constructor
    · intro h
      exact ⟨h.2.2, coprime_of_squarefree_mul $ Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
    · intro h
      exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm), Nat.dvd_mul_right d m, h.1⟩
  · intro h
    have : (d / ν d) * (ν d / d) = 1 := by
      rw [←inv_div, inv_mul_cancel (s.nu_div_self_ne_zero h_dvd)]
    trans ((d / ν d) * (ν d / d) * g d * μ d / S * g m)
    · rw [this, Nat.ArithmeticFunction.IsMultiplicative.map_mul_of_coprime s.selbergTerms_mult $ coprime_comm.mp h.2]
      ring
    ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push_neg; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d in divisors P, if l ∣ d then ν d / d * s.selbergWeights d else 0) =
      if (l : ℝ) ^ 2 ≤ y then g l * μ l / S else 0 :=
  by
  calc
    (∑ d in divisors P, if l ∣ d then ν d / d * s.selbergWeights d else 0) =
        ∑ d in divisors P, ∑ k in divisors P,
          if l ∣ d ∧ d ∣ k ∧ (k : ℝ) ^ 2 ≤ y then g k * (1 / S) * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [← ite_mul_zero_right, ← ite_and_mul_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k in divisors P,if (k : ℝ) ^ 2 ≤ y then
            (∑ d in divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * (1 / S)
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul]
      rw [ sum_mul]; rw [sum_mul]; rw [mul_sum]
      apply sum_congr rfl; intro d _
      rw [← ite_mul_zero_left, ← ite_mul_zero_left]
      rw [←ite_mul_zero_left, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      tauto
      intro _; ring
    _ = if (l : ℝ) ^ 2 ≤ y then g l * μ l / S else 0 := by 
      rw [Aux.sum_intro (f:=fun _ => if (l:ℝ)^2 ≤ y then g l * μ l / S else 0) (divisors P) l hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk)]
      rw [←ite_and, ←ite_mul_zero_left, ←ite_mul_zero_left, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      rw [and_comm, eq_comm]; apply and_congr_right
      intro heq; rw [heq]
      intro h; rw[h.1]; ring

def selbergμPlus : ℕ → ℝ :=
  Sieve.lambdaSquaredOfWeights (s.selbergWeights) 

theorem weight_one_of_selberg : s.selbergWeights 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd P), s.nu_mult.left, s.selbergTerms_mult.left]
  rw [cast_one, ArithmeticFunction.moebius_apply_one, Int.cast_one] 
  rw [mul_one, div_one, mul_one]
  have :
    S = ∑ m : ℕ in divisors P, if (1*(m:ℝ)) ^ 2 ≤ y ∧ m.Coprime 1 then g m else 0 := by
    dsimp only [selbergBoundingSum]; rw [sum_congr rfl]; intro l _
    apply if_ctx_congr _ _ (fun _ => rfl); simp; intro _; rfl
  rw [← this]; apply one_div_mul_cancel
  exact _root_.ne_of_gt s.selbergBoundingSum_pos

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬↑d ≤ y) : s.selbergμPlus d = 0 :=
  by
  apply Sieve.lambdaSquaredOfWeights_eq_zero_of_support _ y _ d hd
  apply s.selbergWeights_eq_zero

def selbergUbSieve : UpperBoundSieve :=
  ⟨s.selbergμPlus, Sieve.upperMoebius_of_lambda_sq (s.selbergWeights) (s.weight_one_of_selberg)⟩

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    s.mainSum (s.selbergμPlus) =
      ∑ l in divisors P,
        1 / g l *
          (∑ d in divisors P, if l ∣ d then ν d / d * s.selbergWeights d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    s.mainSum (s.selbergμPlus) = 1 / S :=
  by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l in divisors P, (if (l : ℝ) ^ 2 ≤ y then g l * (1 / S) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow, ←ite_mul_zero_right]
    apply if_congr Iff.rfl _ rfl
    trans (1/g l * g l * g l * (μ l:ℝ)^2  * (1 / S) ^ 2)
    · ring
    norm_cast; rw [Aux.moebius_sq_eq_one_of_squarefree $ s.squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel $ _root_.ne_of_gt $ s.selbergTerms_pos l $ dvd_of_mem_divisors hl]
    ring
    linarith
  conv => {lhs; congr; {skip}; {ext i; rw [ite_mul_zero_left]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, one_div, mul_inv_cancel]; ring
  apply _root_.ne_of_gt; apply selbergBoundingSum_pos;

lemma eq_gcd_mul_of_dvd_of_coprime {k d m :ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  cases' hkd with r hr
  have hrdvd : r ∣ d; use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d :ℕ} (hkd : k ∣ d) (hk: k ∈ divisors P) (hm: m ∈ divisors P): 
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (↑(k * m):ℝ) ^ 2 ≤ s.level ↔ 
    (↑k * ↑m:ℝ) ^ 2 ≤ s.level ∧ Coprime m d := by
  constructor
  · intro h
    rw [←cast_mul]
    constructor
    · exact h.2.2
    · cases' hkd with r hr
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by aesop_div)] at h
      rw [hr, coprime_comm]; apply Coprime.mul
      apply coprime_of_squarefree_mul $ Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      exact dvd_of_mem_divisors hk; exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by aesop_div)
    · rw[cast_mul]; exact h.1
 
theorem selbergBoundingSum_ge (hdP : d ∣ P) : 
    S ≥ s.selbergWeights d * ↑(μ d) * S := by
  calc _ = (∑ k in divisors P, ∑ l in divisors P, if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ y then g l else 0) := by
        dsimp only [selbergBoundingSum]
        rw [sum_comm, sum_congr rfl]; intro l _
        conv => {rhs; congr; {skip}; {ext k; rw [ite_and]}}
        rw [←Aux.sum_intro]
        rw [mem_divisors]
        exact ⟨Trans.trans (Nat.gcd_dvd_left d l) (hdP), s.prodPrimes_ne_zero⟩ 
  _ ≥ (∑ k in divisors P,
          if k ∣ d then
            g k * ∑ m in divisors P, if (k * m : ℝ) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply ge_of_eq
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    by_cases hkd : k ∣ d
    swap
    · rw [if_neg hkd, sum_eq_zero]; intro l _
      rw [if_neg]
      push_neg; intro h; exfalso
      rw [h] at hkd
      exact hkd $ Nat.gcd_dvd_left d l
    rw [if_pos hkd]
    rw [sum_mul_subst k P, sum_congr rfl]; intro m hm
    rw [←ite_mul_zero_right, ←ite_and]
    apply if_ctx_congr _ _ fun _ => rfl
    · apply s._helper hkd hk hm
    · intro h; 
      apply s.selbergTerms_mult.2
      rw [coprime_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push_neg; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k in divisors P, if k ∣ d 
          then g k * ∑ m in divisors P, if (d * m : ℝ) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by 
    apply sum_le_sum; intro k _
    by_cases hkd : k ∣ d
    swap; rw[if_neg hkd, if_neg hkd]
    rw [if_pos hkd, if_pos hkd]
    apply mul_le_mul le_rfl _ _ (le_of_lt $ s.selbergTerms_pos k $ Trans.trans hkd hdP) 
    apply sum_le_sum; intro m hm
    have : (↑d * ↑m:ℝ) ^ 2 ≤ y ∧ Coprime m d → (↑k * ↑m:ℝ) ^ 2 ≤ s.level ∧ Coprime m d
    · intro h; constructor
      · trans ((d*m:ℝ)^2)
        · norm_cast; apply Aux.nat_sq_mono; apply Nat.mul_le_mul _ le_rfl
          refine Nat.le_of_dvd ?_ hkd
          apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
        · exact h.1
      · exact h.2
    by_cases h : (↑d * ↑m:ℝ) ^ 2 ≤ s.level ∧ Coprime m d
    · rw [if_pos h, if_pos $ this h]
    rw [if_neg h]
    by_cases h' : (↑k * ↑m:ℝ) ^ 2 ≤ s.level ∧ Coprime m d
    · rw [if_pos h']; exact le_of_lt $ s.selbergTerms_pos m $ dvd_of_mem_divisors hm
    · rw [if_neg h']
    apply sum_nonneg; intro m hm
    by_cases h : (↑d * ↑m:ℝ) ^ 2 ≤ s.level ∧ Coprime m d
    · rw [if_pos h]; exact le_of_lt $ s.selbergTerms_pos m $ dvd_of_mem_divisors hm
    · rw [if_neg h]
  _ ≥ _ := by
    apply ge_of_eq
    conv => {lhs; congr; {skip}; ext k; rw [ite_mul_zero_left] }
    rw [←sum_mul, s.conv_selbergTerms_eq_selbergTerms_mul_self_div_nu hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * d / ν d * g d * (∑ m in divisors P, if (d*m:ℝ) ^ 2 ≤ y ∧ Coprime m d then g m else 0))
    · rw [mul_inv_cancel, ←Int.cast_pow, Aux.moebius_sq_eq_one_of_squarefree]
      ring
      exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      exact _root_.ne_of_gt $ s.selbergBoundingSum_pos 
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights :
    ∀ d : ℕ, |s.selbergWeights d| ≤ 1 :=
  by
  let lam := s.selbergWeights
  intro d
  by_cases hdP : d ∣ P
  swap
  · dsimp only [selbergWeights]
    rw [if_neg hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ lam d * ↑(μ d) * S 
  · rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : 1 ≥ lam d * μ d
  apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  rw [ge_iff_le] at this 
  have h := s.selbergWeights_mul_mu_nonneg d hdP
  rw [← abs_of_nonneg h] at this 
  calc
    |lam d| = |lam d| * |(μ d:ℝ)| := by
      rw [← Int.cast_abs, Aux.abs_moebius_eq_one_of_squarefree]
      rw [Int.cast_one, mul_one]; exact s.squarefree_of_dvd_prodPrimes hdP
    _ = |lam d * μ d| := by rw [abs_mul]
    _ ≤ 1 := this

theorem selberg_bound_μPlus (n : ℕ) (hn : n ∈ divisors P) :
    |s.selbergμPlus n| ≤ (3:ℝ) ^ ω n :=
  by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  let lam := s.selbergWeights
  dsimp only [selbergμPlus, lambdaSquaredOfWeights]
  calc
    |∑ d1 in n.divisors, ∑ d2 in n.divisors, if n = d1.lcm d2 then lam d1 * lam d2 else 0| ≤
        ∑ d1 in n.divisors, |∑ d2 in n.divisors, if n = d1.lcm d2 then lam d1 * lam d2 else 0| := ?_
    _ ≤ ∑ d1 in n.divisors, ∑ d2 in n.divisors, |if n = d1.lcm d2 then lam d1 * lam d2 else 0| := ?_
    _ ≤ ∑ d1 in n.divisors, ∑ d2 in n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · apply sum_le_sum; intro d1 _; apply sum_le_sum; intro d2 _
    rw [apply_ite abs, abs_zero, abs_mul]
    dsimp only []; by_cases h : n = d1.lcm d2
    rw [if_pos h, if_pos h]
    apply mul_le_one (s.selberg_bound_weights d1) (abs_nonneg <| lam d2)
      (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · dsimp only []
    rw [← sum_filter, Finset.sum_const, Nat.smul_one_eq_coe]
  · rw [←card_lcm_eq (s.squarefree_of_mem_divisors_prodPrimes hn)]
    congr; ext; rw[eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    s.errSum (s.selbergμPlus) ≤
      ∑ d in divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 :=
  by
  dsimp only [errSum]
  apply sum_le_sum; intro d hd
  by_cases h : (d:ℝ) ≤ y
  · rw [if_pos h]
    apply mul_le_mul _ le_rfl (abs_nonneg <| R d) (pow_nonneg _ <| ω d)
    apply s.selberg_bound_μPlus d hd
    linarith
  · rw [if_neg h]
    rw [s.selbergμPlus_eq_zero d h]
    rw [abs_zero, MulZeroClass.zero_mul]

theorem selberg_bound_simple :
    s.siftedSum ≤
      X / S +
        ∑ d in divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 :=
  by
  let μPlus := s.selbergUbSieve
  calc
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus := s.siftedSum_le_mainSum_errSum_of_UpperBoundSieve μPlus
    _ ≤ _ := ?_
  apply _root_.add_le_add
  have : ⇑μPlus = s.selbergμPlus := rfl
  rw [this]; clear this
  rw [s.selberg_bound_simple_mainSum, mul_one_div]
  refine' s.selberg_bound_simple_errSum

end SelbergSieve