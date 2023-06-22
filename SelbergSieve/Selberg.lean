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

theorem selberg_bounding_sum_nonneg : 0 ≤ S :=
  by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_nonneg
  intro l hl
  rw [mem_filter, mem_divisors] at hl 
  apply le_of_lt; apply s.selbergTerms_pos
  exact hl.left.left

#check S
theorem selberg_bounding_sum_pos :
    0 < S :=
  by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos
  intro l hl
  rw [mem_filter, mem_divisors] at hl 
  apply s.selbergTerms_pos
  exact hl.left.left
  rw [Finset.Nonempty]
  use 1; rw [mem_filter, mem_divisors]
  constructor; constructor; exact one_dvd _; exact s.prodPrimes_ne_zero
  rw [cast_one, one_pow]; linarith [hy]

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    d / ν d * g d * μ d / S *
      ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0
  else 0

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬(d : ℝ) ^ 2 ≤ y) :
    s.selbergWeights d = 0 := by
  dsimp only [selbergWeights]
  by_cases h : d ∣ s.prodPrimes
  swap
  rw [if_neg h]
  rw [if_pos h]
  rw [mul_eq_zero_of_right _]
  rw [Finset.sum_eq_zero]; intro m hm
  rw [if_neg]
  push_neg
  intro hyp
  exfalso
  apply absurd hd
  push_neg
  calc
    ↑d ^ 2 ≤ ↑m ^ 2 * ↑d ^ 2 := ?_
    _ ≤ y := ?_
  have : 1 ≤ (m : ℝ) := by
    norm_cast
    rw [succ_le_iff]
    rw [mem_divisors] at hm 
    rw [zero_lt_iff]
    exact ne_zero_of_dvd_ne_zero hm.2 hm.1
  apply le_mul_of_one_le_left
  exact sq_nonneg (d:ℝ)
  rw [one_le_sq_iff]
  linarith; linarith
  rw [← mul_pow]
  exact hyp

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ s.selbergWeights d * μ d :=
  by
  dsimp only [selbergWeights]
  rw [if_pos hdP]; rw [mul_assoc]
  conv =>
    rhs
    congr
    . skip
    . rw [mul_comm];
  rw [← mul_assoc]
  apply mul_nonneg; rw [div_eq_mul_inv]; rw [mul_comm]
  rw [← mul_assoc]; apply mul_nonneg; rw [mul_comm]; rw [mul_assoc]
  apply mul_nonneg; apply mul_nonneg
  apply div_nonneg
  rw [← cast_zero]; rw [cast_le]; apply Nat.zero_le
  apply le_of_lt; exact s.nu_pos_of_dvd_prodPrimes hdP
  apply le_of_lt; apply s.selbergTerms_pos d hdP
  rw [← sq]; apply sq_nonneg
  rw [inv_nonneg]; exact s.selberg_bounding_sum_nonneg
  apply sum_nonneg; intro m hm
  by_cases h : (↑m * ↑d:ℝ) ^ 2 ≤ y ∧ m.coprime d
  rw [if_pos h]; apply le_of_lt; exact s.selbergTerms_pos m (mem_divisors.mp hm).left
  rw [if_neg h]

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d / d * s.selbergWeights d =
      1 / S * μ d *
        ∑ l in divisors P, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g l else 0 :=
  by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  -- if ¬d ∣ s.prodPrimes then both sides are zero
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]; ring
    intro l hl; rw [mem_divisors] at hl 
    rw [if_neg]; push_neg; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  have hnu_cancel : ν d / ↑d * (↑d / ν d) = 1 :=
    by
    rw [div_mul_div_cancel]; rw [div_self]
    apply _root_.ne_of_gt; exact s.nu_pos_of_dvd_prodPrimes h_dvd
    rw [cast_ne_zero]
    exact ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero h_dvd
  have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero h_dvd
  rw [if_pos h_dvd]
  have :=
    calc
      ν d / ↑d *
            (↑d / ν d * g d * ↑(μ d) / S *
              ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0) =
          1 / S *
            (ν d / ↑d * (↑d / ν d) * g d * ↑(μ d) *
              ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0) :=
        by ring
      _ =
          1 / S *
            (g d * ↑(μ d) *
              ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0) :=
        by rw [hnu_cancel]; ring
  rw [this]; clear this
  suffices
    (g d * ↑(μ d) * ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0) =
      μ d * ∑ l in divisors P, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g l else 0
    by rw [this]; ring
  calc
    (g d * ↑(μ d) * ∑ m in divisors P, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g m else 0) =
        ∑ m in divisors P,
          if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g d * ↑(μ d) * g m else 0 :=
      by
      rw [mul_sum]; apply sum_congr rfl; intro d hd
      rw [ite_mul_zero_right]
    _ =
        ∑ m in divisors P,
          if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g (m * d) * ↑(μ d) else 0 :=
      by
      apply sum_congr rfl; intro m hm
      apply Aux.ite_eq_of_iff_eq _ _ Iff.rfl
      intro h; rw [s.selbergTerms_mult.right m d h.right.right]; ring
    _ =
        ∑ m in divisors P, ∑ l in divisors P,
          if l = m * d ∧ (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g (m * d) * ↑(μ d) else 0 :=
      by
      apply sum_congr rfl; intro m hm
      rw [Aux.sum_intro]; intro h
      rw [mem_divisors] at *
      constructor
      exact coprime.mul_dvd_of_dvd_of_dvd h.right hm.left h_dvd
      exact s.prodPrimes_ne_zero
    _ =
        ∑ l in divisors P, ∑ m in divisors P,
          if m = l / d ∧ d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g l * ↑(μ d) else 0 :=
      by
      rw [sum_comm]; apply sum_congr rfl; intro l hl
      apply sum_congr rfl; intro m hm
      apply Aux.ite_eq_of_iff_eq
      constructor
      · intro h; constructor; rw [Nat.div_eq_of_eq_mul_left _ h.left]
        rw [zero_lt_iff]; exact hd_ne_zero; constructor
        use m; rw [h.left]; ring; rw [h.left]; rw [cast_mul]; exact h.right.left
      · intro h; rcases h with ⟨hmld, hdl, hly⟩
        have hmdl : m * d = l := by rw [hmld]; rw [Nat.div_mul_cancel hdl]
        constructor; rw [hmdl]
        constructor; rw [← cast_mul]; rw [hmdl]; exact hly
        apply Aux.coprime_of_mul_squarefree; rw [hmdl]
        exact s.squarefree_of_mem_divisors_prodPrimes hl
      intro h; rw [h.left.left]
    _ = ∑ l in divisors P, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g l * ↑(μ d) else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [← Aux.sum_intro]
      intro h; rw [mem_divisors] at *; constructor
      calc
        l / d ∣ l := Nat.div_dvd_of_dvd h.left
        _ ∣ s.prodPrimes := hl.left
      exact hl.right
    _ = μ d * ∑ l in divisors P, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g l else 0 :=
      by
      conv =>
        lhs
        congr
        . skip
        . ext
          rw [ite_mul_zero_left]
      rw [← sum_mul]; ring

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
      apply Aux.ite_eq_of_iff_eq; rfl
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
      apply Aux.ite_eq_of_iff_eq
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
      apply Aux.ite_eq_of_iff_eq
      constructor
      · rintro ⟨hky, hlk⟩; rw [hlk]; exact ⟨rfl, hky⟩
      · rintro ⟨hkl, hly⟩; rw [hkl]; exact ⟨hly, rfl⟩
      intro h; rw [h.left.right]; ring
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
    apply Aux.ite_eq_of_iff_eq; simp; intro h; rfl
  rw [← this]; apply one_div_mul_cancel
  apply _root_.ne_of_gt; exact s.selberg_bounding_sum_pos
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
      rw [@Aux.ite_eq_of_iff_eq ℝ _ ((l:ℝ)^2≤y ∧ (l:ℝ)^2≤y) ((l:ℝ)^2≤y) (g l * (μ l:ℝ) / S * (g l * (μ l:ℝ) / S))  (g l ^ 2 * (1 / S) ^ 2) _] 
      swap; tauto
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
          apply s.selberg_bounding_sum_pos


theorem selberg_bound_weights :
    ∀ d : ℕ, |s.selbergWeights d| ≤ 1 :=
  by
  let lam := s.selbergWeights
  intro d
  by_cases hdP : d ∣ s.prodPrimes
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
      apply Aux.ite_eq_of_iff_eq; constructor
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
      intro h; rw [h.right.left]; apply s.selbergTerms_mult.right m k h.right.right.left
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
      rw [sum_congr rfl]; intro k hk; apply Aux.ite_eq_of_iff_eq; exact Iff.rfl
      intro h; rw [sum_congr rfl]; intro m hm
      apply Aux.ite_eq_of_iff_eq
      constructor
      · rintro ⟨hmk, hkd, hmky⟩; constructor; swap
        cases' h.left with r hr
        rw [hr] at hkd ; rw [mul_comm] at hkd ; rw [Nat.gcd_mul_right] at hkd 
        have hk_zero : 0 < k := by
          rw [zero_lt_iff]; apply ne_zero_of_dvd_ne_zero _ h.left
          apply ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
        have : r.coprime m
        calc
          r.gcd m = r.gcd m * k / k := by rw [Nat.mul_div_cancel _ hk_zero]
          _ = k / k := by rw [← hkd]
          _ = 1 := Nat.div_self hk_zero
        rw [hr]; apply coprime.mul_right hmk (coprime_comm.mp this)
        exact hmky
      · rintro ⟨hmky, hmd⟩; constructor
        apply coprime.coprime_dvd_right h.left; exact hmd; constructor
        cases' h.left with r hr; rw [hr]; rw [mul_comm]; rw [Nat.gcd_mul_right]
        have : r.coprime m; apply coprime.coprime_dvd_left (_ : r ∣ d); rw [coprime_comm]
        exact hmd; use k; rw [hr]; ring
        dsimp only [coprime] at this ; rw [this]; ring
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
      apply _root_.ne_of_gt; exact s.selberg_bounding_sum_pos
    _ =
        (if d ∣ s.prodPrimes then
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
  apply le_of_mul_le_mul_of_pos_right this (s.selberg_bounding_sum_pos)
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
      ∑ d in divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |s.rem d| else 0 :=
  by
  dsimp only [errSum]
  apply sum_le_sum; intro d hd
  by_cases h : (d:ℝ) ≤ y
  · rw [if_pos h]
    apply mul_le_mul _ le_rfl (abs_nonneg <| s.rem d) (pow_nonneg _ <| ω d)
    apply s.selberg_bound_μPlus d hd
    linarith
  · rw [if_neg h]
    rw [s.selbergμPlus_eq_zero d h]
    rw [abs_zero, MulZeroClass.zero_mul]

theorem selberg_bound_simple :
    s.siftedSum ≤
      s.totalMass / S +
        ∑ d in divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |s.rem d| else 0 :=
  by
  let μPlus := s.selbergUbSieve
  calc
    s.siftedSum ≤ s.totalMass * s.mainSum μPlus + s.errSum μPlus := s.siftedSum_le_mainSum_errSum_of_UpperBoundSieve μPlus
    _ ≤ _ := ?_
  apply _root_.add_le_add
  have : ⇑μPlus = s.selbergμPlus := rfl
  rw [this]; clear this
  rw [s.selberg_bound_simple_mainSum, mul_one_div]
  refine' s.selberg_bound_simple_errSum

end SelbergSieve

