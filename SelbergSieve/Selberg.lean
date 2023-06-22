/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
import SelbergSieve.Sieve

noncomputable section

open scoped BigOperators Classical Sieve

open Finset Real Nat Sieve.UpperBoundSieve Nat.ArithmeticFunction

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

namespace Sieve

-- TODO: remove, temporary
local notation "g" => selbergTerms

--set_option profiler true
@[simp]
def selbergBoundingSumAtLevel (s : Sieve) (y : ℝ) : ℝ :=
  ∑ l in s.prodPrimes.divisors, if (l : ℝ) ^ 2 ≤ y then g s l else 0

theorem selberg_bounding_sum_nonneg (s : Sieve) (y : ℝ) : 0 ≤ s.selbergBoundingSumAtLevel y :=
  by
  dsimp only [selbergBoundingSumAtLevel]
  rw [← sum_filter]
  apply sum_nonneg
  intro l hl
  rw [mem_filter, mem_divisors] at hl 
  apply le_of_lt; apply s.selbergTerms_pos
  exact hl.left.left

theorem selberg_bounding_sum_pos (s : Sieve) (y : ℝ) (hy : 1 ≤ y) :
    0 < s.selbergBoundingSumAtLevel y :=
  by
  dsimp only [selbergBoundingSumAtLevel]
  rw [← sum_filter]
  apply sum_pos
  intro l hl
  rw [mem_filter, mem_divisors] at hl 
  apply s.selbergTerms_pos
  exact hl.left.left
  rw [Finset.Nonempty]
  use 1; rw [mem_filter, mem_divisors]
  constructor; constructor; exact one_dvd _; exact s.prodPrimes_ne_zero
  rw [cast_one, one_pow]; linarith

def selbergWeights (s : Sieve) (y : ℝ) : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    d / s.nu d * g s d * μ d / selbergBoundingSumAtLevel s y *
      ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0
  else 0

theorem selbergWeights_eq_zero (s : Sieve) (y : ℝ) (d : ℕ) (hd : ¬(d : ℝ) ^ 2 ≤ y) :
    s.selbergWeights y d = 0 := by
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

theorem selbergWeights_mul_mu_nonneg (s : Sieve) (y : ℝ) (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ s.selbergWeights y d * μ d :=
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
  rw [inv_nonneg]; exact s.selberg_bounding_sum_nonneg y
  apply sum_nonneg; intro m hm
  by_cases h : (↑m * ↑d:ℝ) ^ 2 ≤ y ∧ m.coprime d
  rw [if_pos h]; apply le_of_lt; exact s.selbergTerms_pos m (mem_divisors.mp hm).left
  rw [if_neg h]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (m l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (l m) -/
--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (s : Sieve) (y : ℝ) (d : ℕ) :
    s.nu d / d * s.selbergWeights y d =
      1 / s.selbergBoundingSumAtLevel y * μ d *
        ∑ l in s.prodPrimes.divisors, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g s l else 0 :=
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
  let S := s.selbergBoundingSumAtLevel y
  have hnu_cancel : s.nu d / ↑d * (↑d / s.nu d) = 1 :=
    by
    rw [div_mul_div_cancel]; rw [div_self]
    apply _root_.ne_of_gt; exact s.nu_pos_of_dvd_prodPrimes h_dvd
    rw [cast_ne_zero]
    exact ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero h_dvd
  have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero h_dvd
  rw [if_pos h_dvd]
  have :=
    calc
      s.nu d / ↑d *
            (↑d / s.nu d * g s d * ↑(μ d) / S *
              ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0) =
          1 / S *
            (s.nu d / ↑d * (↑d / s.nu d) * g s d * ↑(μ d) *
              ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0) :=
        by ring
      _ =
          1 / S *
            (g s d * ↑(μ d) *
              ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0) :=
        by rw [hnu_cancel]; ring
  rw [this]; clear this
  suffices
    (g s d * ↑(μ d) * ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0) =
      μ d * ∑ l in s.prodPrimes.divisors, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g s l else 0
    by rw [this]; ring
  calc
    (g s d * ↑(μ d) * ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0) =
        ∑ m in s.prodPrimes.divisors,
          if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s d * ↑(μ d) * g s m else 0 :=
      by
      rw [mul_sum]; apply sum_congr rfl; intro d hd
      rw [ite_mul_zero_right]
    _ =
        ∑ m in s.prodPrimes.divisors,
          if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s (m * d) * ↑(μ d) else 0 :=
      by
      apply sum_congr rfl; intro m hm
      apply Aux.ite_eq_of_iff_eq _ _ Iff.rfl
      intro h; rw [s.hg_mult.right m d h.right.right]; ring
    _ =
        ∑ m in s.prodPrimes.divisors, ∑ l in s.prodPrimes.divisors,
          if l = m * d ∧ (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s (m * d) * ↑(μ d) else 0 :=
      by
      apply sum_congr rfl; intro m hm
      rw [Aux.sum_intro]; intro h
      rw [mem_divisors] at *
      constructor
      exact coprime.mul_dvd_of_dvd_of_dvd h.right hm.left h_dvd
      exact s.prodPrimes_ne_zero
    _ =
        ∑ l in s.prodPrimes.divisors, ∑ m in s.prodPrimes.divisors,
          if m = l / d ∧ d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g s l * ↑(μ d) else 0 :=
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
    _ = ∑ l in s.prodPrimes.divisors, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g s l * ↑(μ d) else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [← Aux.sum_intro]
      intro h; rw [mem_divisors] at *; constructor
      calc
        l / d ∣ l := Nat.div_dvd_of_dvd h.left
        _ ∣ s.prodPrimes := hl.left
      exact hl.right
    _ = μ d * ∑ l in s.prodPrimes.divisors, if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g s l else 0 :=
      by
      conv =>
        lhs
        congr
        . skip
        . ext
          rw [ite_mul_zero_left]
      rw [← sum_mul]; ring

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (d k) -/
theorem selbergWeights_diagonalisation (s : Sieve) (y : ℝ) (l : ℕ) (hl : l ∈ s.prodPrimes.divisors) :
    (∑ d in s.prodPrimes.divisors, if l ∣ d then s.nu d / d * s.selbergWeights y d else 0) =
      if (l : ℝ) ^ 2 ≤ y then g s l * μ l / s.selbergBoundingSumAtLevel y else 0 :=
  by
  let S := s.selbergBoundingSumAtLevel y
  calc
    (∑ d in s.prodPrimes.divisors, if l ∣ d then s.nu d / d * s.selbergWeights y d else 0) =
        ∑ d in s.prodPrimes.divisors,
          if l ∣ d then
            1 / S * μ d * ∑ k in s.prodPrimes.divisors, if d ∣ k ∧ (k : ℝ) ^ 2 ≤ y then g s k else 0
          else 0 :=
      by
      conv =>
        lhs
        congr
        . skip
        . ext
          rw [selbergWeights_eq_dvds_sum]
    _ =
        ∑ d in s.prodPrimes.divisors, ∑ k in s.prodPrimes.divisors,
          if l ∣ d ∧ d ∣ k ∧ (k : ℝ) ^ 2 ≤ y then g s k * (1 / S) * (μ d:ℝ) else 0 :=
      by
      apply sum_congr rfl; intro d hd
      rw [← boole_mul]; rw [mul_sum]; rw [mul_sum]
      apply sum_congr rfl; intro k hk
      rw [← ite_mul_zero_right]; rw [← ite_and_mul_zero]
      apply Aux.ite_eq_of_iff_eq; rfl
      intro h; ring
    _ =
        ∑ k in s.prodPrimes.divisors,
          if (k : ℝ) ^ 2 ≤ y then
            (∑ d in s.prodPrimes.divisors, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g s k * (1 / S)
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
    _ = ∑ k in s.prodPrimes.divisors, if k = l ∧ (l : ℝ) ^ 2 ≤ y then g s l * μ l / S else 0 :=
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
    _ = if (l : ℝ) ^ 2 ≤ y then g s l * μ l / S else 0 := by rw [← Aux.sum_intro]; intro h; exact hl

def selbergμPlus (s : Sieve) (y : ℝ) : ℕ → ℝ :=
  lambdaSquaredOfWeights (s.selbergWeights y)

theorem weight_one_of_selberg (s : Sieve) (y : ℝ) (hy : 1 ≤ y) : s.selbergWeights y 1 = 1 :=
  by
  dsimp only [selbergWeights]
  rw [if_pos]
  rw [s.nu_mult.left]
  rw [s.hg_mult.left]
  rw [cast_one]; rw [ArithmeticFunction.moebius_apply_one]; rw [Int.cast_one]; rw [mul_one];
  rw [div_one]; rw [mul_one]
  have :
    s.selbergBoundingSumAtLevel y =
      ∑ m : ℕ in s.prodPrimes.divisors, ite (((m:ℝ) * 1) ^ 2 ≤ y ∧ m.coprime 1) (g s m) 0 :=
    by
    dsimp only [selbergBoundingSumAtLevel]; rw [sum_congr rfl]; intro l hl
    apply Aux.ite_eq_of_iff_eq; simp; intro h; rfl
  rw [← this]; apply one_div_mul_cancel
  apply _root_.ne_of_gt; exact s.selberg_bounding_sum_pos y hy
  exact one_dvd _

theorem selbergμPlus_eq_zero (s : Sieve) (y : ℝ) (d : ℕ) (hd : ¬↑d ≤ y) : s.selbergμPlus y d = 0 :=
  by
  apply lambdaSquaredOfWeights_eq_zero_of_support _ y _ d hd
  apply s.selbergWeights_eq_zero

def selbergUbSieve (s : Sieve) (y : ℝ) (hy : 1 ≤ y) : UpperBoundSieve :=
  ⟨s.selbergμPlus y, upperMoebius_of_lambda_sq (s.selbergWeights y) (s.weight_one_of_selberg y hy)⟩

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form (s : Sieve) (y : ℝ) :
    s.mainSum (s.selbergμPlus y) =
      ∑ l in s.prodPrimes.divisors,
        1 / g s l *
          (∑ d in s.prodPrimes.divisors, if l ∣ d then s.nu d / d * s.selbergWeights y d else 0) ^ 2 :=
  by apply lambda_sq_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum (s : Sieve) (y : ℝ) (hy : 1 ≤ y) :
    s.mainSum (s.selbergμPlus y) = 1 / s.selbergBoundingSumAtLevel y :=
  by
  let S := s.selbergBoundingSumAtLevel y
  rw [mainSum_eq_diag_quad_form]
  calc
    ∑ l in s.prodPrimes.divisors,
          1 / g s l *
            (∑ d in s.prodPrimes.divisors, if l ∣ d then s.nu d / ↑d * s.selbergWeights y d else 0) ^ 2 =
        ∑ l in s.prodPrimes.divisors, 1 / g s l * (if (l : ℝ) ^ 2 ≤ y then g s l * μ l / S else 0) ^ 2 :=
      by
      apply sum_congr rfl; intro l hl
      rw [s.selbergWeights_diagonalisation y l hl]
    _ = ∑ l in s.prodPrimes.divisors, 1 / g s l * if (l : ℝ) ^ 2 ≤ y then g s l ^ 2 * (1 / S) ^ 2 else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [sq]
      rw [← ite_and_mul_zero]
      rw [@Aux.ite_eq_of_iff_eq ℝ _ ((l:ℝ)^2≤y ∧ (l:ℝ)^2≤y) ((l:ℝ)^2≤y) (g s l * (μ l:ℝ) / S * (g s l * (μ l:ℝ) / S))  (g s l ^ 2 * (1 / S) ^ 2) _] 
      swap; tauto
      intro h
      calc
        g s l * ↑(μ l) / S * (g s l * ↑(μ l) / S) = g s l ^ 2 * ↑(μ l) ^ 2 * (1 / S) ^ 2 := by ring
        _ = g s l ^ 2 * (1 / S) ^ 2 := by
          rw [← Int.cast_pow]; rw [Aux.moebius_sq_eq_one_of_squarefree (s.squarefree_of_mem_divisors_prodPrimes hl)]
          rw [Int.cast_one]; ring
    _ = ∑ l in s.prodPrimes.divisors, (if (l : ℝ) ^ 2 ≤ y then g s l else 0) * (1 / S) ^ 2 :=
      by
      apply sum_congr rfl; intro l hl
      rw [ite_mul_zero_left]; rw [← mul_assoc]
      rw [← ite_mul_zero_right]; rw [sq <| g s l]; rw [← mul_assoc]
      rw [mem_divisors] at hl 
      rw [cast_one, one_div_mul_cancel]; rw [one_mul]; apply _root_.ne_of_gt; exact s.selbergTerms_pos l hl.left
    _ = 1 / S := by
      rw [← sum_mul]; rw [sq]; rw [← mul_assoc]
      calc
        S * (1 / S) * (1 / S) = 1 / S := by
          rw [mul_one_div_cancel]; ring; apply _root_.ne_of_gt
          apply s.selberg_bounding_sum_pos y hy

example (x y z : ℝ) (hx : 0 < x) (h : y ≤ z) : x * y ≤ x * z :=
  (mul_le_mul_left hx).mpr h

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k m l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k l) -/
theorem selberg_bound_weights (s : Sieve) (y : ℝ) (hy : 1 ≤ y) :
    ∀ d : ℕ, |s.selbergWeights y d| ≤ 1 :=
  by
  let S := s.selbergBoundingSumAtLevel y
  let lam := s.selbergWeights y
  intro d
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · dsimp only [selbergWeights]
    rw [if_neg hdP]; simp only [zero_le_one, abs_zero]
  have : S ≥ lam d * ↑(μ d) * S
  calc
    (∑ l in s.prodPrimes.divisors, if (l : ℝ) ^ 2 ≤ y then g s l else 0) =
        ∑ k in s.prodPrimes.divisors, ∑ l in s.prodPrimes.divisors, if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ y then g s l else 0 :=
      by
      rw [sum_comm]; apply sum_congr rfl; intro l hl
      rw [← Aux.sum_intro s.prodPrimes.divisors ((l : ℝ) ^ 2 ≤ y)]
      intro h_le; rw [mem_divisors]
      constructor; exact dvd_trans (Nat.gcd_dvd_left d l) hdP; exact s.prodPrimes_ne_zero
    _ =
        ∑ k in s.prodPrimes.divisors, ∑ m in s.prodPrimes.divisors, ∑ l in s.prodPrimes.divisors,
          if l = m * k ∧ m.coprime k ∧ k = d.gcd (m * k) ∧ (m * k : ℝ) ^ 2 ≤ y then g s m * g s k
          else 0 :=
      by
      apply sum_congr rfl; intro k hk; rw [sum_comm]; apply sum_congr rfl; intro l hl
      rw [Aux.sum_intro s.prodPrimes.divisors _ _ (l / k)]
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
      intro h; rw [h.right.left]; apply s.hg_mult.right m k h.right.right.left
      intro h; rw [h.left]; rw [mem_divisors] at *; constructor
      exact dvd_trans (div_dvd_of_dvd <| Nat.gcd_dvd_right d l) hl.left; exact s.prodPrimes_ne_zero
    _ =
        ∑ k in s.prodPrimes.divisors,
          g s k *
            ∑ m in s.prodPrimes.divisors,
              if m.coprime k ∧ k = d.gcd (m * k) ∧ (m * k : ℝ) ^ 2 ≤ y then g s m else 0 :=
      by
      apply sum_congr rfl; intro k hk; rw [mul_sum]; apply sum_congr rfl; intro m hm
      conv =>
        rhs
        rw [mul_comm];
      rw [← ite_mul_zero_left]; rw [Aux.sum_intro]
      intro h; rw [mem_divisors] at *; constructor; apply coprime.mul_dvd_of_dvd_of_dvd h.left
      exact hm.left; exact hk.left; exact s.prodPrimes_ne_zero
    _ =
        ∑ k in s.prodPrimes.divisors,
          if k ∣ d then
            g s k *
              ∑ m in s.prodPrimes.divisors,
                if m.coprime k ∧ k = d.gcd (m * k) ∧ (m * k : ℝ) ^ 2 ≤ y then g s m else 0
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
        ∑ k in s.prodPrimes.divisors,
          if k ∣ d then
            g s k * ∑ m in s.prodPrimes.divisors, if (m * k : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0
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
        ∑ k in s.prodPrimes.divisors,
          if k ∣ d then
            g s k * ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0
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
        (∑ k in s.prodPrimes.divisors, if k ∣ d then g s k else 0) *
          ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0 :=
      by rw [sum_mul]; apply sum_congr rfl; intro k hk; rw [ite_mul_zero_left]
    _ =
        g s d * (↑d / s.nu d) *
          ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0 :=
      by rw [s.conv_g_eq hdP]
    _ =
        (↑d / s.nu d * g s d * μ d / S *
              ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0) *
            μ d *
          S :=
      by
      conv =>
        lhs
        rw [← one_mul (g s d)]
        rw [← Int.cast_one]
        rw [← Aux.moebius_sq_eq_one_of_squarefree (Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree)]
        rw [Int.cast_pow]
        rw [← one_mul (g s d)]
      rw [← div_self (_ : S ≠ 0)]; ring
      apply _root_.ne_of_gt; exact s.selberg_bounding_sum_pos y hy
    _ =
        (if d ∣ s.prodPrimes then
              d / s.nu d * g s d * μ d / S *
                ∑ m in s.prodPrimes.divisors, if (m * d : ℝ) ^ 2 ≤ y ∧ m.coprime d then g s m else 0
            else 0) *
            ↑(μ d) *
          S :=
      by rw [if_pos hdP]
  conv at this =>
    lhs
    rw [← one_mul S]
  replace this : 1 ≥ lam d * μ d
  apply le_of_mul_le_mul_of_pos_right this (s.selberg_bounding_sum_pos y hy)
  rw [ge_iff_le] at this 
  have h := s.selbergWeights_mul_mu_nonneg y d hdP
  rw [← abs_of_nonneg h] at this 
  calc
    |lam d| = |lam d| * |(μ d:ℝ)| := by
      rw [← Int.cast_abs]; rw [Aux.abs_moebius_eq_one_of_squarefree]
      rw [Int.cast_one]; rw [mul_one]; exact s.squarefree_of_dvd_prodPrimes hdP
    _ = |lam d * μ d| := by rw [abs_mul]
    _ ≤ 1 := this

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (d1 d2) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (d1 d2) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (d1 d2) -/
theorem selberg_bound_μPlus (s : Sieve) (y : ℝ) (hy : 1 ≤ y) (n : ℕ) (hn : n ∈ s.prodPrimes.divisors) :
    |s.selbergμPlus y n| ≤ (3:ℝ) ^ ω n :=
  by
  let f : ℕ → ℕ → ℝ := fun x y : ℕ => if n = x.lcm y then 1 else 0
  let lam := s.selbergWeights y
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
    mul_le_one (s.selberg_bound_weights y hy d1) (abs_nonneg <| lam d2)
      (s.selberg_bound_weights y hy d2)
  rw [if_neg h, if_neg h]
  rw [← Finset.sum_product']
  dsimp only []
  rw [← sum_filter, Finset.sum_const, Nat.smul_one_eq_coe]
  rw [Aux.card_lcm_eq (s.squarefree_of_mem_divisors_prodPrimes hn), cast_pow]
  norm_num

theorem selberg_bound_simple_errSum (s : Sieve) (y : ℝ) (hy : 1 ≤ y) :
    s.errSum (s.selbergμPlus y) ≤
      ∑ d in s.prodPrimes.divisors, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |s.rem d| else 0 :=
  by
  dsimp only [errSum]
  apply sum_le_sum; intro d hd
  by_cases h : (d:ℝ) ≤ y
  · rw [if_pos h]
    apply mul_le_mul _ le_rfl (abs_nonneg <| s.rem d) (pow_nonneg _ <| ω d)
    apply s.selberg_bound_μPlus y hy d hd
    linarith
  · rw [if_neg h]
    rw [s.selbergμPlus_eq_zero y d h]
    rw [abs_zero, MulZeroClass.zero_mul]

theorem selberg_bound_simple (s : Sieve) (y : ℝ) (hy : 1 ≤ y) :
    s.siftedSum ≤
      s.totalMass / s.selbergBoundingSumAtLevel y +
        ∑ d in s.prodPrimes.divisors, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |s.rem d| else 0 :=
  by
  let μPlus := s.selbergUbSieve y hy
  calc
    s.siftedSum ≤ s.totalMass * s.mainSum μPlus + s.errSum μPlus := s.upper_bound_main_err μPlus
    _ ≤ _ := ?_
  apply _root_.add_le_add
  have : ⇑μPlus = s.selbergμPlus y := rfl
  rw [this]; clear this
  rw [s.selberg_bound_simple_mainSum y hy, mul_one_div]
  refine' s.selberg_bound_simple_errSum y hy

end Sieve

