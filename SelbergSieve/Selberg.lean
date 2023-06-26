/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
import SelbergSieve.SieveLemmas

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
local notation "ν" => s.nu
local notation "P" => s.prodPrimes
local notation "a" => s.weights
local notation "X" => s.totalMass
local notation "R" => s.rem
local notation "g" => s.selbergTerms
local notation "y" => s.level
local notation "hy" => s.one_le_level

--set_option profiler true
@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l in divisors P, if (l : ℝ) ^ 2 ≤ y then g l else 0

local notation "S" => s.selbergBoundingSum

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
      ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0
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

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ s.selbergWeights d * μ d :=
  by
  dsimp only [selbergWeights]
  rw [if_pos hdP]; rw [mul_assoc]
  trans ((μ d :ℝ)^2 * (d/ν d) * g d / S * ∑ m in divisors P,
          if (m * d:ℝ) ^ 2 ≤ y ∧ coprime m d then g m else 0)
  swap; apply le_of_eq; ring
  apply mul_nonneg; apply div_nonneg; apply mul_nonneg; apply mul_nonneg
  · apply sq_nonneg
  · rw [←inv_div, inv_nonneg]
    exact le_of_lt $ s.nu_div_self_pos hdP
  · exact le_of_lt $ s.selbergTerms_pos d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  by_cases h : (↑m * ↑d:ℝ) ^ 2 ≤ y ∧ m.coprime d
  · rw [if_pos h]; exact le_of_lt $ s.selbergTerms_pos m (dvd_of_mem_divisors hm)
  · rw [if_neg h]


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
  -- change of 
  trans (∑ m in divisors P, ∑ l in divisors P, if l=m*d 
    then 1 / selbergBoundingSum s * ↑(μ d) * if (m*d:ℝ)^2 ≤ y ∧ m.coprime d then s.selbergTerms l else 0
    else 0)
  · apply sum_congr rfl; intro m hm
    rw [sum_eq_single (m*d), if_pos rfl]
    repeat rw [←ite_mul_zero_right]
    apply if_ctx_congr Iff.rfl _ fun _ => rfl
    intro h
    rw [s.selbergTerms_mult.2 _ _ h.2]
    trans ((d / ν d) * (ν d / d) * g d * μ d / S * g m)
    · ring
    have : (d / ν d) * (ν d / d) = 1 := by
      rw [←inv_div, inv_mul_cancel (s.nu_div_self_ne_zero h_dvd)]
    rw [this]; ring
    intro l _ hlmd; rw [if_neg hlmd]
    intro h
    have h_cop : ¬ m.coprime d
    · revert h; contrapose!; intro h_cop
      rw [←Nat.coprime.lcm_eq_mul h_cop, mem_divisors, Nat.lcm_dvd_iff]
      exact ⟨⟨dvd_of_mem_divisors hm, h_dvd⟩, s.prodPrimes_ne_zero⟩
    rw [if_pos rfl, if_neg, mul_zero]
    push_neg; exact fun _ => h_cop
  rw [sum_comm]
  apply sum_congr rfl; intro l hl
  repeat rw [←ite_mul_zero_right]
  rw [sum_eq_single (l/d)]
  rw [ite_mul_zero_right, ←ite_and, ←ite_mul_zero_right]
  apply if_congr _ rfl rfl
  constructor
  · intro h; constructor
    · use (l/d); rw [mul_comm]; exact h.1
    · rw [h.1, cast_mul]; exact h.2.1
  · intro h; constructor
    · rw [Nat.div_mul_cancel h.1]
    constructor
    · norm_cast; rw [Nat.div_mul_cancel h.1, cast_pow]; exact h.2
    · apply Aux.coprime_of_mul_squarefree; rw [Nat.div_mul_cancel h.1]
      exact Squarefree.squarefree_of_dvd (dvd_of_mem_divisors hl) s.prodPrimes_squarefree
  · intro m _ hm
    rw [if_neg]; by_contra h
    rw [h, Nat.mul_div_cancel] at hm
    contradiction
    rw [zero_lt_iff]; exact ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero h_dvd 
  · intro h; rw [if_neg]
    revert h; contrapose!; intro h
    rw [mem_divisors] at *
    have : l / d ∣ l := ⟨d,h⟩
    exact ⟨Trans.trans this hl.1, s.prodPrimes_ne_zero⟩ 

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d in divisors P, if l ∣ d then ν d / d * s.selbergWeights d else 0) =
      if (l : ℝ) ^ 2 ≤ y then g l * μ l / S else 0 :=
  by
  calc
    (∑ d in divisors P, if l ∣ d then ν d / d * s.selbergWeights d else 0) =
        ∑ d in divisors P,
          if l ∣ d then
            1 / S * μ d * ∑ k in divisors P, if d ∣ k ∧ (k : ℝ) ^ 2 ≤ y then g k else 0
          else 0 :=
      by
      conv =>
        lhs
        congr
        . skip
        . ext
          rw [selbergWeights_eq_dvds_sum]
    _ =
        ∑ d in divisors P, ∑ k in divisors P,
          if l ∣ d ∧ d ∣ k ∧ (k : ℝ) ^ 2 ≤ y then g k * (1 / S) * (μ d:ℝ) else 0 :=
      by
      apply sum_congr rfl; intro d hd
      rw [← boole_mul]; rw [mul_sum]; rw [mul_sum]
      apply sum_congr rfl; intro k hk
      rw [← ite_mul_zero_right]; rw [← ite_and_mul_zero]
      apply if_ctx_congr _ _ (fun _ => rfl); rfl
      intro h; ring
    _ =
        ∑ k in divisors P,
          if (k : ℝ) ^ 2 ≤ y then
            (∑ d in divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * (1 / S)
          else 0 :=
      by
      rw [sum_comm]; apply sum_congr rfl; intro k hk
      conv =>
        rhs
        rw [← boole_mul]
      rw [ sum_mul]; rw [sum_mul]; rw [mul_sum]
      apply sum_congr rfl; intro d hd
      conv =>
        rhs
        congr
        . skip
        . rw [← ite_mul_zero_left, ← ite_mul_zero_left]
      rw [← ite_and_mul_zero]
      apply if_ctx_congr _ _ (fun _ => rfl)
      constructor
      · rintro ⟨hld, hdk, hky⟩; exact ⟨hky, hld, hdk⟩
      · rintro ⟨hky, hld, hdk⟩; exact ⟨hld, hdk, hky⟩
      intro h; ring
    _ = ∑ k in divisors P, if k = l ∧ (l : ℝ) ^ 2 ≤ y then g l * μ l / S else 0 :=
      by
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l k]
      rw [← ite_mul_zero_left]; rw [← ite_mul_zero_left]
      rw [← ite_and]
      apply symm
      apply if_ctx_congr _ _ (fun _ => rfl)
      constructor
      · rintro ⟨hkl, hly⟩; rw [hkl]; exact ⟨hly, rfl⟩
      · rintro ⟨hky, hlk⟩; rw [hlk]; exact ⟨rfl, hky⟩
      intro h; rw [h.right]; ring
      rw [mem_divisors] at hk ; exact hk.left
    _ = if (l : ℝ) ^ 2 ≤ y then g l * μ l / S else 0 := by rw [← Aux.sum_intro]; intro h; exact hl

def selbergμPlus : ℕ → ℝ :=
  Sieve.lambdaSquaredOfWeights (s.selbergWeights) 

theorem weight_one_of_selberg : s.selbergWeights 1 = 1 :=
  by
  dsimp only [selbergWeights]
  rw [if_pos]
  rw [s.nu_mult.left]
  rw [s.selbergTerms_mult.left]
  rw [cast_one]; rw [ArithmeticFunction.moebius_apply_one]; rw [Int.cast_one]; rw [mul_one];
  rw [div_one]; rw [mul_one]
  have :
    S =
      ∑ m : ℕ in divisors P, ite (((m:ℝ) * 1) ^ 2 ≤ y ∧ m.coprime 1) (g m) 0 :=
    by
    dsimp only [selbergBoundingSum]; rw [sum_congr rfl]; intro l hl
    apply if_ctx_congr _ _ (fun _ => rfl); simp; intro h; rfl
  rw [← this]; apply one_div_mul_cancel
  apply _root_.ne_of_gt; exact s.selbergBoundingSum_pos
  exact one_dvd _

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
  calc
    ∑ l in divisors P,
          1 / g l *
            (∑ d in divisors P, if l ∣ d then ν d / ↑d * s.selbergWeights d else 0) ^ 2 =
        ∑ l in divisors P, 1 / g l * (if (l : ℝ) ^ 2 ≤ y then g l * μ l / S else 0) ^ 2 :=
      by
      apply sum_congr rfl; intro l hl
      rw [s.selbergWeights_diagonalisation l hl]
    _ = ∑ l in divisors P, 1 / g l * if (l : ℝ) ^ 2 ≤ y then g l ^ 2 * (1 / S) ^ 2 else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [sq]
      rw [← ite_and_mul_zero]
      rw [if_ctx_congr (b:=((l:ℝ)^2≤y ∧ (l:ℝ)^2≤y)) (c:=((l:ℝ)^2≤y)) _ _ (fun _ => rfl)]
      tauto
      intro h
      calc
        g l * ↑(μ l) / S * (g l * ↑(μ l) / S) = g l ^ 2 * ↑(μ l) ^ 2 * (1 / S) ^ 2 := by ring
        _ = g l ^ 2 * (1 / S) ^ 2 := by
          rw [← Int.cast_pow]; rw [Aux.moebius_sq_eq_one_of_squarefree (s.squarefree_of_mem_divisors_prodPrimes hl)]
          rw [Int.cast_one]; ring
    _ = ∑ l in divisors P, (if (l : ℝ) ^ 2 ≤ y then g l else 0) * (1 / S) ^ 2 :=
      by
      apply sum_congr rfl; intro l hl
      rw [ite_mul_zero_left]; rw [← mul_assoc]
      rw [← ite_mul_zero_right]; rw [sq <| g l]; rw [← mul_assoc]
      rw [mem_divisors] at hl 
      rw [cast_one, one_div_mul_cancel]; rw [one_mul]; apply _root_.ne_of_gt; exact s.selbergTerms_pos l hl.left
    _ = 1 / S := by
      rw [← sum_mul]; rw [sq]; rw [← mul_assoc]
      calc
        S * (1 / S) * (1 / S) = 1 / S := by
          rw [mul_one_div_cancel]; ring; apply _root_.ne_of_gt
          apply s.selbergBoundingSum_pos


theorem selberg_bound_weights :
    ∀ d : ℕ, |s.selbergWeights d| ≤ 1 :=
  by
  let lam := s.selbergWeights
  intro d
  by_cases hdP : d ∣ P
  swap
  · dsimp only [selbergWeights]
    rw [if_neg hdP]; simp only [zero_le_one, abs_zero]
  have : S ≥ lam d * ↑(μ d) * S
  calc
    (∑ l in divisors P, if (l : ℝ) ^ 2 ≤ y then g l else 0) =
        ∑ k in divisors P, ∑ l in divisors P, if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ y then g l else 0 :=
      by
      rw [sum_comm]; apply sum_congr rfl; intro l hl
      rw [← Aux.sum_intro (divisors P) ((l : ℝ) ^ 2 ≤ y)]
      intro h_le; rw [mem_divisors]
      constructor; exact dvd_trans (Nat.gcd_dvd_left d l) hdP; exact s.prodPrimes_ne_zero
    _ =
        ∑ k in divisors P, ∑ m in divisors P, ∑ l in divisors P,
          if l = m * k ∧ m.coprime k ∧ k = d.gcd (m * k) ∧ (m * k : ℝ) ^ 2 ≤ y then g m * g k
          else 0 :=
      by
      apply sum_congr rfl; intro k hk; rw [sum_comm]; apply sum_congr rfl; intro l hl
      rw [Aux.sum_intro (divisors P) _ _ (l / k)]
      apply sum_congr rfl; intro m hm
      apply if_ctx_congr _ _ (fun _ => rfl); constructor
      · rintro ⟨hmlk, hkdl, hly⟩
        have : l = m * k := by
          rw [mul_comm]; apply Nat.eq_mul_of_div_eq_right
          rw [hkdl]; apply Nat.gcd_dvd_right d l; exact eq_comm.mp hmlk
        constructor; exact this
        constructor; apply Aux.coprime_of_mul_squarefree; rw [← this];
        exact s.squarefree_of_mem_divisors_prodPrimes hl
        constructor; rw [← this]; exact hkdl
        rw [← cast_mul]; rw [← this]; exact hly
      · rintro ⟨hlmk, hmk, hkd, hmky⟩
        constructor; rw [eq_comm]; apply Nat.div_eq_of_eq_mul_left; rw [zero_lt_iff]
        rw [mem_divisors] at hk ; apply ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hk.left
        exact hlmk; constructor; rw [← hlmk] at hkd ; exact hkd
        rw [← cast_mul] at hmky ; rw [hlmk]; exact hmky
      intro h; rw [h.left]; apply s.selbergTerms_mult.right m k h.right.left
      intro h; rw [h.left]; rw [mem_divisors] at *; constructor
      exact dvd_trans (div_dvd_of_dvd <| Nat.gcd_dvd_right d l) hl.left; exact s.prodPrimes_ne_zero
    _ =
        ∑ k in divisors P,
          g k *
            ∑ m in divisors P,
              if m.coprime k ∧ k = d.gcd (m * k) ∧ (m * k : ℝ) ^ 2 ≤ y then g m else 0 :=
      by
      apply sum_congr rfl; intro k hk; rw [mul_sum]; apply sum_congr rfl; intro m hm
      conv =>
        rhs
        rw [mul_comm];
      rw [← ite_mul_zero_left]; rw [Aux.sum_intro]
      intro h; rw [mem_divisors] at *; constructor; apply coprime.mul_dvd_of_dvd_of_dvd h.left
      exact hm.left; exact hk.left; exact s.prodPrimes_ne_zero
    _ =
        ∑ k in divisors P,
          if k ∣ d then
            g k *
              ∑ m in divisors P,
                if m.coprime k ∧ k = d.gcd (m * k) ∧ (m * k : ℝ) ^ 2 ≤ y then g m else 0
          else 0 :=
      by
      apply sum_congr rfl; intro k hk
      by_cases hkd : k ∣ d
      · rw [if_pos hkd]
      · rw [if_neg hkd]; rw [sum_eq_zero]; ring
        intro m hm; rw [if_neg]; push_neg; intro hmk hgcd; exfalso
        have h : d.gcd (m * k) ∣ d := Nat.gcd_dvd_left d (m * k)
        rw [← hgcd] at h ; exact hkd h
    _ =
        ∑ k in divisors P,
          if k ∣ d then
            g k * ∑ m in divisors P, if (m * k : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0
          else 0 :=
      by
      rw [sum_congr rfl]; intro k hk; apply symm; apply if_ctx_congr _ _ (fun _ => rfl); exact Iff.rfl
      intro h; rw [sum_congr rfl]; intro m hm
      apply if_ctx_congr _ _ (fun _ => rfl)
      constructor
      · rintro ⟨hmky, hmd⟩; constructor
        apply coprime.coprime_dvd_right h; exact hmd; constructor
        cases' h with r hr; rw [hr]; rw [mul_comm]; rw [Nat.gcd_mul_right]
        have : r.coprime m; apply coprime.coprime_dvd_left (_ : r ∣ d); rw [coprime_comm]
        exact hmd; use k; rw [hr]; ring
        dsimp only [coprime] at this ; rw [this]; ring
        exact hmky
      · rintro ⟨hmk, hkd, hmky⟩; constructor; swap
        cases' h with r hr
        rw [hr] at hkd ; rw [mul_comm] at hkd ; rw [Nat.gcd_mul_right] at hkd 
        have hk_zero : 0 < k := by
          rw [zero_lt_iff]; apply ne_zero_of_dvd_ne_zero _ (⟨r, hr⟩:k∣d)
          apply ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
        have : r.coprime m
        calc
          r.gcd m = r.gcd m * k / k := by rw [Nat.mul_div_cancel _ hk_zero]
          _ = k / k := by rw [← hkd]
          _ = 1 := Nat.div_self hk_zero
        rw [hr]; apply coprime.mul_right hmk (coprime_comm.mp this)
        exact hmky
      exact fun _ => rfl
    _ ≥
        ∑ k in divisors P,
          if k ∣ d then
            g k * ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0
          else 0 :=
      by
      rw [ge_iff_le]; apply sum_le_sum; intro k hk
      by_cases hkd : k ∣ d
      swap
      · rw [if_neg hkd]; rw [if_neg hkd]
      rw [if_pos hkd]; rw [if_pos hkd]
      apply (mul_le_mul_left (s.selbergTerms_pos k _)).mpr
      apply sum_le_sum; intro m hm
      have hmk : 0 ≤ (m : ℝ) * ↑k := 
        by 
        rw [← cast_mul]; rw [← cast_zero]; rw [cast_le];
        apply Nat.zero_le
      have hmd : (m : ℝ) * ↑k ≤ (m : ℝ) * ↑d :=
        by
        rw [← cast_mul]; rw [← cast_mul]; rw [cast_le]
        apply Nat.mul_le_mul_of_nonneg_left; apply le_of_dvd _ hkd
        rw [zero_lt_iff]; apply ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
      by_cases h : (↑m * ↑d:ℝ) ^ 2 ≤ y ∧ m.coprime d
      · rw [if_pos h]
        have h' : (↑m * ↑k:ℝ) ^ 2 ≤ y ∧ m.coprime d
        constructor; swap; exact h.right
        calc
          (↑m * ↑k) ^ 2 ≤ (↑m * ↑d) ^ 2 := by apply sq_le_sq'; linarith; linarith
          _ ≤ y := h.left
        rw [if_pos h']
      · rw [if_neg h]
        by_cases h_if : (↑m * ↑k:ℝ) ^ 2 ≤ y ∧ m.coprime d
        rw [if_pos h_if]; apply le_of_lt; apply s.selbergTerms_pos _ (mem_divisors.mp hm).left
        rw [if_neg h_if]
      exact (mem_divisors.mp hk).left
    _ =
        (∑ k in divisors P, if k ∣ d then g k else 0) *
          ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0 :=
      by rw [sum_mul]; apply sum_congr rfl; intro k hk; rw [ite_mul_zero_left]
    _ =
        g d * (↑d / ν d) *
          ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0 :=
      by rw [s.conv_selbergTerms_eq_selbergTerms_mul_self_div_nu hdP]
    _ =
        (↑d / ν d * g d * μ d / S *
              ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0) *
            μ d *
          S :=
      by
      conv =>
        lhs
        rw [← one_mul (g d)]
        rw [← Int.cast_one]
        rw [← Aux.moebius_sq_eq_one_of_squarefree (Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree)]
        rw [Int.cast_pow]
        rw [← one_mul (g d)]
      rw [← div_self (_ : S ≠ 0)]; ring
      apply _root_.ne_of_gt; exact s.selbergBoundingSum_pos
    _ =
        (if d ∣ P then
              d / ν d * g d * μ d / S *
                ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0
            else 0) *
            ↑(μ d) *
          S :=
      by rw [if_pos hdP]
  conv at this =>
    lhs
    rw [← one_mul S]
  replace this : 1 ≥ lam d * μ d
  apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  rw [ge_iff_le] at this 
  have h := s.selbergWeights_mul_mu_nonneg d hdP
  rw [← abs_of_nonneg h] at this 
  calc
    |lam d| = |lam d| * |(μ d:ℝ)| := by
      rw [← Int.cast_abs]; rw [Aux.abs_moebius_eq_one_of_squarefree]
      rw [Int.cast_one]; rw [mul_one]; exact s.squarefree_of_dvd_prodPrimes hdP
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
    _ = (3:ℝ) ^ ω n := ?_
  apply abs_sum_le_sum_abs
  apply sum_le_sum; intro d1 hd1; apply abs_sum_le_sum_abs
  apply sum_le_sum; intro d1 hd1; apply sum_le_sum; intro d2 hd2
  rw [apply_ite abs, abs_zero, abs_mul]
  dsimp only []; by_cases h : n = d1.lcm d2
  rw [if_pos h, if_pos h]
  apply
    mul_le_one (s.selberg_bound_weights d1) (abs_nonneg <| lam d2)
      (s.selberg_bound_weights d2)
  rw [if_neg h, if_neg h]
  rw [← Finset.sum_product']
  dsimp only []
  rw [← sum_filter, Finset.sum_const, Nat.smul_one_eq_coe]
  rw [Aux.card_lcm_eq (s.squarefree_of_mem_divisors_prodPrimes hn), cast_pow]
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

