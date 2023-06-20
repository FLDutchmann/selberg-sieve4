/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Squarefree
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction
import SelbergSieve.AuxResults

noncomputable section

open scoped BigOperators Classical

open Finset Real Nat Aux

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option profiler -/
set_option profiler true

-- TODO: rename ω to ν so as to not clash with arithmetic_function
-- TODO: make ω an arithmetic_function so we can re-use is_multiplicative  
-- one should think of a as weights given to the elements of A,
-- values of a n for n not in A do not affect any of the results
structure Sieve where mk ::
  A : Finset ℕ
  P : ℕ
  hP : Squarefree P
  a : ℕ → ℝ
  ha_nonneg : ∀ n : ℕ, 0 ≤ a n
  X : ℝ
  ω : ArithmeticFunction ℝ
  hω_mult : ω.IsMultiplicative
  hω_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ω p
  hω_size : ∀ p : ℕ, p.Prime → p ∣ P → ω p < p

namespace Sieve

theorem hP_ne_zero (s : Sieve) : s.P ≠ 0 :=
  Squarefree.ne_zero s.hP

theorem sqfree_of_dvd_P (s : Sieve) {d : ℕ} (hd : d ∣ s.P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.hP

theorem sqfree_of_mem_dvd_P (s : Sieve) {d : ℕ} (hd : d ∈ s.P.divisors) : Squarefree d :=
  by
  simp only [Nat.mem_divisors, Ne.def] at hd 
  exact Squarefree.squarefree_of_dvd hd.left s.hP

theorem hω_pos_of_dvd_P (s : Sieve) {d : ℕ} (hl : d ∣ s.P) : 0 < s.ω d := by
  calc
    0 < ∏ p in d.factors.toFinset, s.ω p :=
      by
      apply prod_pos
      intro p hpd; rw [List.mem_toFinset] at hpd 
      have hp_prime : p.Prime := prime_of_mem_factors hpd
      have hp_dvd : p ∣ s.P := dvd_trans (dvd_of_mem_factors hpd) hl
      exact s.hω_pos_of_prime p hp_prime hp_dvd
    _ = s.ω d := prod_factors_of_mult s.ω s.hω_mult (Squarefree.squarefree_of_dvd hl s.hP)

theorem hω_ne_zero_of_mem_dvd_P (s : Sieve) {d : ℕ} (hd : d ∈ s.P.divisors) : s.ω d ≠ 0 :=
  by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd 
  apply s.hω_pos_of_dvd_P hd.left

@[simp]
def multSum (s : Sieve) (d : ℕ) : ℝ :=
  ∑ n in s.A, if d ∣ n then s.a n else 0

-- A_d = ω(d)/d X + R_d
@[simp]
def R (s : Sieve) (d : ℕ) : ℝ :=
  s.multSum d - s.ω d / d * s.X

theorem multSum_eq_main_err (s : Sieve) (d : ℕ) : s.multSum d = s.ω d / d * s.X + s.R d :=
  by
  dsimp [R]
  ring

def siftedSum (s : Sieve) : ℝ :=
  ∑ d in s.A, if s.P.coprime d then s.a d else 0

@[simp]
def δ (n : ℕ) : ℝ :=
  if n = 1 then 1 else 0

-- mathport name: moebius
-- Introduce notation from nat.arithmetic_function because ω defined
-- in that file would lead to confusion with s.ω.
-- TODO rename s.ω and undo this local notation.
scoped notation "μ" => Nat.ArithmeticFunction.moebius

-- mathport name: card_distinct_factors
scoped notation "ν" => Nat.ArithmeticFunction.cardDistinctFactors

theorem siftedSum_as_delta (s : Sieve) : s.siftedSum = ∑ d in s.A, s.a d * δ (Nat.gcd s.P d) :=
  by
  cases' s with A P hP a ha_pos X ω
  dsimp only [siftedSum]
  apply sum_congr rfl
  intro d hd
  dsimp only [Nat.coprime, δ] at *
  by_cases h : P.gcd d = 1
  · rw [if_pos h]
    rw [if_pos h]
    ring
  · rw [if_neg h]
    rw [if_neg h]
    ring

def hω_size_of_dvd_P (s : Sieve) : ∀ d : ℕ, d ∣ s.P → d ≠ 1 → s.ω d < d :=
  by
  intro d hdP hd_ne_one
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.hP
  calc
    s.ω d = ∏ p in d.factors.toFinset, s.ω p :=
      eq_comm.mp (prod_factors_of_mult s.ω s.hω_mult hd_sq)
    _ < ∏ p in d.factors.toFinset, ↑p :=
      by
      have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero s.hP_ne_zero hdP
      apply prod_le_prod_of_nonempty
      · intro p hp; rw [List.mem_toFinset] at hp 
        rw [mem_factors hd_ne_zero] at hp 
        apply s.hω_pos_of_prime p hp.left (dvd_trans hp.right hdP)
      · intro p hpd; rw [List.mem_toFinset] at hpd ; rw [mem_factors hd_ne_zero] at hpd 
        apply s.hω_size p hpd.left (dvd_trans hpd.right hdP)
      · dsimp [Finset.Nonempty]
        conv =>
          congr
          ext
          rw [List.mem_toFinset]
          rw [Nat.mem_factors hd_ne_zero]
        exact Nat.exists_prime_and_dvd hd_ne_one
    _ = ↑d := by
      rw [prod_factors_of_mult]; constructor; push_cast ; ring
      intro x y _
      suffices ↑(x * y) = (x:ℝ) * ↑y 
        by exact this
      rw [cast_mul]
      exact hd_sq
      

theorem hω_over_d_mult (s : Sieve) : Multiplicative (fun d => s.ω d / ↑d) :=
  by
  apply div_mult_of_mult
  exact s.hω_mult
  exact coe_mult
  intro n hn
  rw [Nat.cast_ne_zero]
  exact _root_.ne_of_gt hn


-- Used in statement of the simple form of the selberg bound
def g (s : Sieve) (d : ℕ) : ℝ :=
  s.ω d / d * ∏ p in d.factors.toFinset, 1 / (1 - s.ω p / p)

-- S = ∑_{l|P, l≤√y} g(l)
-- Facts about g
theorem hg_pos (s : Sieve) (l : ℕ) (hl : l ∣ s.P) : 0 < s.g l :=
  by
  have hl_sq : Squarefree l := Squarefree.squarefree_of_dvd hl s.hP
  dsimp only [g]
  apply mul_pos
  apply div_pos
  apply lt_of_le_of_ne
  apply le_of_lt
  exact s.hω_pos_of_dvd_P hl
  apply ne_comm.mp; apply _root_.ne_of_gt; exact s.hω_pos_of_dvd_P hl
  suffices : 0 < l; exact cast_pos.mpr this
  rw [zero_lt_iff]; exact Squarefree.ne_zero hl_sq
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  rw [List.mem_toFinset] at hp 
  have hp_prime : p.Prime := prime_of_mem_factors hp
  have hp_dvd : p ∣ s.P := by
    calc
      p ∣ l := Nat.dvd_of_mem_factors hp
      _ ∣ s.P := hl
  have : s.ω p < p := s.hω_size p hp_prime hp_dvd
  have hp_pos : 0 < (p : ℝ) :=
    by
    suffices 0 < p by exact cast_pos.mpr this
    exact Nat.Prime.pos hp_prime
  have hp_ne_zero : (p : ℝ) ≠ 0 := ne_comm.mp (ne_of_lt hp_pos)
  rw [← zero_lt_mul_right hp_pos]
  calc
    0 < ↑p - s.ω p := by linarith only [this]
    _ = (1 - s.ω p / ↑p) * ↑p := by
      conv =>
        lhs
        rw [← (div_mul_cancel (s.ω p) hp_ne_zero : s.ω p / p * p = s.ω p)];
      ring

theorem hg_mult (s : Sieve) : Multiplicative s.g :=
  by
  have : s.g = (fun d => s.ω d / ↑d) * fun d => ∏ p in d.factors.toFinset, 1 / (1 - s.ω p / p) :=
    by ext d; rfl
  rw [this]
  apply mult_mul_of_mult
  exact s.hω_over_d_mult
  exact mult_prod_factors _
set_option profiler true
theorem rec_g_eq_conv_moebius_omega (s : Sieve) (l : ℕ) (hl : Squarefree l)
    (hω_nonzero : s.ω l ≠ 0) : 1 / s.g l = ∑ d in l.divisors, (μ <| l / d) * (d / s.ω d) :=
  by
  dsimp only [g]
  simp only [one_div, mul_inv, inv_div, inv_inv, Finset.prod_congr, Finset.prod_inv_distrib]
  rw [prod_eq_moebius_sum fun d => s.ω d / (d : ℝ)]
  · rw [mul_sum]
    calc
      ∑ d in l.divisors, ↑l / s.ω l * (↑(μ d) * (s.ω d / ↑d)) =
          ∑ d in l.divisors, ↑(μ d) * (↑l / ↑d) * (s.ω d / s.ω l) :=
        by apply sum_congr rfl; intro d hd; ring
      _ = ∑ d in l.divisors, ↑(μ d) * ↑(l / d) * (1 / (s.ω l / s.ω d)) :=
        by
        apply sum_congr rfl; intro d hd
        rw [mem_divisors] at hd 
        rw [← Nat.cast_div hd.left]
        rw [one_div_div]
        rw [Nat.cast_ne_zero]
        exact ne_zero_of_dvd_ne_zero hd.right hd.left
      _ = ∑ d in l.divisors, ↑(μ d) * (↑(l / d) / s.ω (l / d)) :=
        by
        apply sum_congr rfl; intro d hd
        rw [mem_divisors] at hd 
        rw [div_mult_of_dvd_squarefree s.ω s.hω_mult l d hd.left hl]
        ring
        revert hω_nonzero; contrapose!
        exact multiplicative_zero_of_zero_dvd s.ω s.hω_mult hl hd.left
      _ = l.divisors.sum fun d => ↑(μ d) * (↑(l / d) / s.ω (l / d)) := rfl
      _ = l.divisors.sum fun d => μ (l / d) * (↑d / s.ω d) :=
        by
        rw [← Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (↑e / s.ω e)]
        rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (↑e / s.ω e)]
  exact s.hω_over_d_mult
  exact hl

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (l k) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k l) -/
theorem omega_eq_conv_rec_g (s : Sieve) (d : ℕ) (hdP : d ∣ s.P) :
    (d : ℝ) / s.ω d = ∑ l in s.P.divisors, if l ∣ d then 1 / s.g l else 0 :=
  by
  -- Problem, these identities only hold on l ∣ P, so can't use standard moebius inversion results,
  rw [eq_comm]
  calc
    (∑ l in s.P.divisors, if l ∣ d then 1 / s.g l else 0) =
        ∑ l in s.P.divisors, if l ∣ d then ∑ k in l.divisors, (μ <| l / k) * (k / s.ω k) else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [s.rec_g_eq_conv_moebius_omega l (s.sqfree_of_mem_dvd_P hl) (s.hω_ne_zero_of_mem_dvd_P hl)]
    _ =
        ∑ l in s.P.divisors,
          if l ∣ d then ∑ k in s.P.divisors, if k ∣ l then (μ <| l / k) * (k / s.ω k) else 0
          else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [mem_divisors] at hl ; rw [← sum_over_dvd_ite s.hP_ne_zero hl.left]
    _ =
        ∑ l in s.P.divisors,
          (∑ k in s.P.divisors, if k ∣ l then (μ <| l / k) * (k / s.ω k) else 0) *
            if l ∣ d then 1 else 0 :=
      by
      conv =>
        rhs
        congr
        . skip
        . ext
          rw [mul_boole]
    _ =
        ∑ l in s.P.divisors, ∑ k in s.P.divisors, 
          (if k ∣ l then (μ <| l / k) * (k / s.ω k) else 0) * if l ∣ d then 1 else 0 :=
      by apply sum_congr rfl; intro l hl; rw [sum_mul]
    _ = ∑ k in s.P.divisors, ∑ l in s.P.divisors, (if k ∣ l ∧ l ∣ d then (μ <| l / k) * (k / s.ω k) else 0) :=
      by
      rw [sum_comm]
      apply sum_congr rfl; intro l hl
      apply sum_congr rfl; intro k hk
      rw [← ite_and_mul_zero]
      apply ite_eq_of_iff_eq _ _ Iff.rfl; intro; ring
    _ = ∑ k in s.P.divisors, ∑ l in s.P.divisors, (if k ∣ l ∧ l ∣ d then (μ l:ℝ) / (μ k:ℝ) else 0) * (k / s.ω k) :=
      by
      apply sum_congr rfl; intro k hk
      apply sum_congr rfl; intro l hl
      rw [←ite_mul_zero_left] 
      apply ite_eq_of_iff_eq _ _ Iff.rfl
      rintro ⟨h, _⟩
      have := Nat.ArithmeticFunction.isMultiplicative_moebius
      suffices (μ (l / k):ℝ) = (μ l:ℝ) / (μ k:ℝ)
        by rw [this]
      
      -- SLOW SLOW SLOW SLOW
      rw [div_mult_of_dvd_squarefree (fun n ↦ ↑(μ n))]
      constructor; simp
      intro x y hxy; norm_cast
      apply Nat.ArithmeticFunction.IsMultiplicative.map_mul_of_coprime this hxy
      exact h.left
      exact s.sqfree_of_mem_dvd_P hl
      suffices μ k ≠ 0 
        by simpa using this
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      exact s.sqfree_of_mem_dvd_P hk
    _ =
        ∑ k in s.P.divisors,
          (∑ l in s.P.divisors, if k ∣ l ∧ l ∣ d then (μ l:ℝ) else 0) / (μ k:ℝ) * (k / s.ω k) :=
      by
      apply sum_congr rfl; intro k hk
      conv =>
        lhs
        congr
        . skip
        . ext
          rw [div_eq_mul_inv, ite_mul_zero_left]
      rw [← sum_mul, ← sum_mul, ← div_eq_mul_inv]
    _ = ∑ k in s.P.divisors, (if k = d then (μ k:ℝ) else 0) / (μ k:ℝ) * (k / s.ω k) :=
      by
      apply sum_congr rfl; intro k hk; rw [← Int.cast_zero]
      conv =>
        lhs
        congr
        congr
        congr
        . skip
        . ext
          conv => rw [← Int.cast_ite];
      rw [← Int.cast_sum]
      --rw [(rfl : μ = arithmetic_function.moebius)]
      classical
      rw [moebius_inv_dvd_lower_bound s.hP k d hdP]
      rw [← Int.cast_ite]
    _ = ↑d / s.ω d := by
      rw [Finset.sum_eq_single d]
      rw [if_pos rfl]; rw [div_self]; ring
      rw [Int.cast_ne_zero]
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      exact Squarefree.squarefree_of_dvd hdP s.hP
      intro k hk hkd; rw [if_neg hkd]; ring
      intro hd; rw [mem_divisors] at hd 
      exfalso; push_neg at hd 
      exact s.hP_ne_zero (hd hdP)

theorem conv_g_eq (s : Sieve) {d : ℕ} (hd : d ∣ s.P) :
    (∑ l in s.P.divisors, if l ∣ d then s.g l else 0) = s.g d * (↑d / s.ω d) := by
  calc
    (∑ l in s.P.divisors, if l ∣ d then s.g l else 0) =
        ∑ l in s.P.divisors, if l ∣ d then s.g (d / l) else 0 :=
      by
      rw [← sum_over_dvd_ite s.hP_ne_zero hd]
      rw [← Nat.sum_divisorsAntidiagonal fun x y => s.g x]
      rw [Nat.sum_divisorsAntidiagonal' fun x y => s.g x]
      rw [sum_over_dvd_ite s.hP_ne_zero hd]
    _ = s.g d * ∑ l in s.P.divisors, if l ∣ d then 1 / s.g l else 0 :=
      by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [← ite_mul_zero_right]; apply ite_eq_of_iff_eq _ _ Iff.rfl; intro h
      rw [← div_mult_of_dvd_squarefree s.g s.hg_mult d l]; ring
      exact h.left; apply Squarefree.squarefree_of_dvd hd s.hP
      apply _root_.ne_of_gt; rw [mem_divisors] at hl ; apply hg_pos; exact hl.left
    _ = s.g d * (↑d / s.ω d) := by rw [← s.omega_eq_conv_rec_g d hd]

def UpperMoebius (μ_plus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, δ n ≤ ∑ d in n.divisors, μ_plus d

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμ_plus : UpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

def mainSum (s : Sieve) (μ_plus : ℕ → ℝ) : ℝ :=
  ∑ d in s.P.divisors, μ_plus d * s.ω d / d

def errSum (s : Sieve) (μ_plus : ℕ → ℝ) : ℝ :=
  ∑ d in s.P.divisors, |μ_plus d| * |s.R d|

theorem upper_bound_of_upperBoundSieve (s : Sieve) (μ_plus : UpperBoundSieve) :
    s.siftedSum ≤ ∑ d in s.P.divisors, μ_plus d * s.multSum d :=
  by
  have hμ : ∀ n, δ n ≤ ∑ d in n.divisors, μ_plus d := μ_plus.hμ_plus
  rw [siftedSum_as_delta]
  calc
    ∑ n in s.A, s.a n * δ (s.P.gcd n) ≤ ∑ n in s.A, s.a n * ∑ d in (s.P.gcd n).divisors, μ_plus d :=
      by
      apply Finset.sum_le_sum
      intro n hnA
      exact mul_le_mul_of_nonneg_left (hμ (s.P.gcd n)) (s.ha_nonneg n)
    _ = ∑ n in s.A, ∑ d in (s.P.gcd n).divisors, s.a n * μ_plus d :=
      by
      apply sum_congr rfl; intro n hnA
      exact mul_sum
    _ = ∑ n in s.A, ∑ d in s.P.divisors, if d ∣ n then s.a n * μ_plus d else 0 :=
      by
      apply sum_congr rfl; intro n hnA
      apply sum_over_dvd s.hP_ne_zero (gcd_dvd s.P n).left
      · intro d hd
        have : ¬d ∣ n := by
          by_contra h
          exact hd.right (Nat.dvd_gcd_iff.mpr ⟨hd.left, h⟩)
        exact if_neg this
      · intro d hd
        have : d ∣ n := dvd_trans hd (gcd_dvd s.P n).right
        exact if_pos this
    _ = ∑ d in s.P.divisors, ∑ n in s.A, if d ∣ n then s.a n * μ_plus d else 0 := Finset.sum_comm
    _ = ∑ d in s.P.divisors, ∑ n in s.A, μ_plus d * if d ∣ n then s.a n else 0 :=
      by
      apply sum_congr rfl; intro d hdP
      apply sum_congr rfl; intro n hnA
      rw [ite_mul_zero_left]; ring
    _ = ∑ d in s.P.divisors, μ_plus d * ∑ n in s.A, if d ∣ n then s.a n else 0 :=
      by
      apply sum_congr rfl; intro d hdP
      rw [eq_comm]
      apply mul_sum

theorem upper_bound_main_err (s : Sieve) (μ_plus : UpperBoundSieve) :
    s.siftedSum ≤ s.X * s.mainSum μ_plus + s.errSum μ_plus :=
  by
  dsimp only [mainSum, errSum]
  have err_bound :
    ∑ d in s.P.divisors, μ_plus d * s.R d ≤ ∑ d in s.P.divisors, |μ_plus d| * |s.R d| := by
    calc
      ∑ d in s.P.divisors, μ_plus d * s.R d ≤ |∑ d in s.P.divisors, μ_plus d * s.R d| :=
        le_abs.mpr (Or.intro_left _ le_rfl)
      _ ≤ ∑ d in s.P.divisors, |μ_plus d * s.R d| :=
        (abs_sum_le_sum_abs (fun d => μ_plus d * s.R d) s.P.divisors)
      _ = ∑ d in s.P.divisors, |μ_plus d| * |s.R d| :=
        by
        apply sum_congr rfl; intro d hdP
        exact abs_mul (μ_plus d) (s.R d)
  calc
    s.siftedSum ≤ ∑ d in s.P.divisors, μ_plus d * s.multSum d :=
      s.upper_bound_of_upperBoundSieve μ_plus
    _ = ∑ d in s.P.divisors, μ_plus d * (s.ω d / d * s.X + s.R d) :=
      by
      apply sum_congr rfl; intro d hdP
      rw [s.multSum_eq_main_err]
    _ = ∑ d in s.P.divisors, (μ_plus d * s.ω d / d * s.X + μ_plus d * s.R d) := by
      apply sum_congr rfl; intro d hdP; ring
    _ = ∑ d in s.P.divisors, μ_plus d * s.ω d / d * s.X + ∑ d in s.P.divisors, μ_plus d * s.R d :=
      sum_add_distrib
    _ = s.X * ∑ d in s.P.divisors, μ_plus d * s.ω d / ↑d + ∑ d in s.P.divisors, μ_plus d * s.R d :=
      by rw [← sum_mul]; rw [mul_comm]
    _ ≤
        s.X * ∑ d in s.P.divisors, μ_plus d * s.ω d / ↑d +
          ∑ d in s.P.divisors, |μ_plus d| * |s.R d| :=
      by linarith

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (d1 d2) -/
def lambdaSquaredOfWeights (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

theorem lambdaSquaredOfWeights_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬(d : ℝ) ^ 2 ≤ y → w d = 0) :
    ∀ d : ℕ, ¬↑d ≤ y → lambdaSquaredOfWeights w d = 0 :=
  by
  by_cases hy : 0 ≤ y
  swap
  · intro d hd
    push_neg at hd hy 
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw; push_neg
      have : (0:ℝ) ≤ (d' : ℝ) ^ 2 := by norm_num
      linarith
    dsimp only [lambdaSquaredOfWeights]
    apply sum_eq_zero; intro d1 hd1
    apply sum_eq_zero; intro d2 hd2
    rw [this d1, this d2]
    simp only [ite_self, eq_self_iff_true, MulZeroClass.mul_zero]
  intro d hd
  dsimp only [lambdaSquaredOfWeights]
  apply sum_eq_zero; intro d1 hd1; apply sum_eq_zero; intro d2 hd2
  by_cases h : d = d1.lcm d2
  swap; rw [if_neg h]
  rw [if_pos h]
  wlog hass : d1 ≤ d2
  · push_neg at hass 
    rw [mul_comm]
    refine' this w y hw hy d hd d2 hd2 d1 hd1 _ (le_of_lt hass)
    rw [Nat.lcm_comm]; exact h
  have hcases : ¬(d2 : ℝ) ^ 2 ≤ y := by
    by_contra hyp
    apply absurd hd; push_neg
    rw [← abs_of_nonneg (_ : 0 ≤ (d : ℝ))]
    apply abs_le_of_sq_le_sq _ hy
    calc
      ↑d ^ 2 = ↑(d1.lcm d2) ^ 2 := ?_
      _ ≤ (↑d1 * ↑d2) ^ 2 := ?_
      _ ≤ (d2:ℝ) ^ (2:ℕ) * (d2:ℝ) ^ (2:ℕ) := ?_
      _ ≤ y ^ 2 := ?_
    rw [h]
    norm_cast
    apply nat_sq_mono
    apply Nat.div_le_self
    norm_cast
    rw [← mul_pow]; apply nat_sq_mono;
    apply mul_le_mul hass le_rfl (Nat.zero_le d2) (Nat.zero_le d2)
    --rw [sq]
    conv =>
      rhs
      rw [sq]
    apply mul_le_mul hyp hyp (sq_nonneg _) hy
    rw [← cast_zero, cast_le]
    exact _root_.zero_le d
  rw [hw d2 hcases, MulZeroClass.mul_zero]

theorem lambda_sq_mainSum_eq_quad_form (s : Sieve) (w : ℕ → ℝ) :
    s.mainSum (lambdaSquaredOfWeights w) =
      ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
        s.ω d1 / d1 * w d1 * s.ω d2 / d2 * w d2 * d1.gcd d2 / s.ω (d1.gcd d2) :=
  by
  dsimp only [mainSum, lambdaSquaredOfWeights]
  calc
    ∑ d in s.P.divisors,
          (∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = d1.lcm d2 then w d1 * w d2 else 0) * s.ω d / ↑d =
        ∑ d in s.P.divisors,
          (∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = d1.lcm d2 then w d1 * w d2 else 0) * (s.ω d / ↑d) :=
      by apply sum_congr rfl; intro d hdP; ring
    _ =
        ∑ d in s.P.divisors, ∑ d1 in d.divisors, ∑ d2 in d.divisors, 
          (if d = d1.lcm d2 then w d1 * w d2 else 0) * (s.ω d / ↑d) :=
      by apply sum_congr rfl; intro d hdP; rw [sum_mul]; apply sum_congr rfl; intro d1 hd1d; rw [sum_mul]
    _ =
        ∑ d in s.P.divisors, ∑ d1 in d.divisors, ∑ d2 in d.divisors, 
          if d = d1.lcm d2 then w d1 * w d2 * s.ω d / ↑d else 0 :=
      by 
      apply sum_congr rfl; intro d hdP; apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl;
      intro d2 hd2
      rw [← ite_mul_zero_left]
      apply ite_eq_of_iff_eq _ _ Iff.rfl
      rintro ⟨h, _⟩; ring 
    _ =
        ∑ d in s.P.divisors, ∑ d1 in s.P.divisors, ∑ d2 in d.divisors, 
          if d = d1.lcm d2 then w d1 * w d2 * s.ω d / ↑d else 0 :=
      by 
      apply sum_congr rfl; intro d hdP
      apply sum_over_dvd s.hP_ne_zero
      · rw [mem_divisors] at hdP ; exact hdP.left
      · intro d1 hd1
        apply sum_eq_zero
        intro d2 hd2
        have : d ≠ d1.lcm d2 := 
          by by_contra h; rw [h] at hd1; exact hd1.right (Nat.dvd_lcm_left d1 d2)
        rw [if_neg this]
      · intro d1 hd1; rfl
    _ = ∑ d in s.P.divisors, ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors, 
          if d = d1.lcm d2 then w d1 * w d2 * s.ω d / ↑d else 0 :=
      by
      apply sum_congr rfl; intro d hdP
      apply sum_congr rfl; intro d1 hd1P
      apply sum_over_dvd s.hP_ne_zero
      · rw [mem_divisors] at hdP ; exact hdP.left
      · intro d2 hd2
        have : d ≠ d1.lcm d2 := 
          by by_contra h; rw [h] at hd2; exact hd2.right (Nat.dvd_lcm_right d1 d2)
        rw [if_neg this]
      · exact fun _ _ => rfl
    _ = ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors, ∑ d in s.P.divisors,  if d = d1.lcm d2 then w d1 * w d2 * s.ω d / ↑d else 0 := 
      by rw [sum_comm]; apply sum_congr rfl; intro d1 hd1; rw [sum_comm]
    _ =
        ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors, ∑ d in s.P.divisors, 
          if d = d1.lcm d2 ∧ True then w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2) else 0 :=
      by 
      apply sum_congr rfl; intro d1 hd1P; apply sum_congr rfl; intro d2 hd2; apply sum_congr rfl;
      intro d hd
      apply ite_eq_of_iff_eq
      · rw [and_true_iff]
      rintro ⟨h, _⟩; rw [← h]
    _ =
        ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
          if True then w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2) else 0 :=
      by 
      apply sum_congr rfl; intro d1 hd1P; apply sum_congr rfl; intro d2 hd2P
      rw [← sum_intro s.P.divisors True (w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2))]
      rw [mem_divisors] at hd1P hd2P 
      intro
      rw [mem_divisors]; constructor
      exact Nat.lcm_dvd_iff.mpr ⟨hd1P.left, hd2P.left⟩
      exact hd1P.right
    _ = ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors, 
          w d1 * w d2 * s.ω (d1.lcm d2) / ↑(d1.lcm d2) :=
      by 
      apply sum_congr rfl; intro d1 _; apply sum_congr rfl; intro d2 _
      rw [if_pos trivial]
    _ =
        ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
          s.ω d1 / ↑d1 * w d1 * s.ω d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / s.ω (d1.gcd d2) :=
      by 
      apply sum_congr rfl; intro d1 hd1P; apply sum_congr rfl; intro d2 hd2P
      have : s.ω (d1.lcm d2) = s.ω d1 * s.ω d2 / s.ω (d1.gcd d2) :=
        by
        by_cases h_zero : s.ω (d1.gcd d2) = 0
        · rw [h_zero]; simp only [div_zero]
          have : d1.gcd d2 ∣ d1.lcm d2
          calc
            d1.gcd d2 ∣ d1 := Nat.gcd_dvd_left d1 d2
            _ ∣ d1.lcm d2 := Nat.dvd_lcm_left d1 d2
          exact
            multiplicative_zero_of_zero_dvd s.ω s.hω_mult
              (lcm_squarefree_of_squarefree (s.sqfree_of_mem_dvd_P hd1P)
                (s.sqfree_of_mem_dvd_P hd2P))
              this h_zero
        · rw [eq_div_iff_mul_eq h_zero]; rw [eq_comm]
          exact
            mult_gcd_lcm_of_squarefree s.ω s.hω_mult d1 d2 (s.sqfree_of_mem_dvd_P hd1P)
              (s.sqfree_of_mem_dvd_P hd2P)
      rw [this]
      dsimp only [Nat.lcm]
      rw [Nat.cast_div (Aux.gcd_dvd_mul d1 d2)]
      rw [Nat.cast_mul]
      calc
        w d1 * w d2 * (s.ω d1 * s.ω d2 / s.ω (d1.gcd d2)) / (↑d1 * ↑d2 / ↑(d1.gcd d2)) =
            w d1 * w d2 * s.ω d1 * s.ω d2 / s.ω (d1.gcd d2) / (↑d1 * ↑d2 / ↑(d1.gcd d2)) :=
          by ring
        _ = w d1 * w d2 * s.ω d1 * s.ω d2 / s.ω (d1.gcd d2) / (↑d1 * ↑d2) * ↑(d1.gcd d2) := by
          rw [← div_mul]
        _ = w d1 * w d2 * s.ω d1 * s.ω d2 / s.ω (d1.gcd d2) / ↑d1 / ↑d2 * ↑(d1.gcd d2) := by
          rw [← div_div]
        _ = s.ω d1 / ↑d1 * w d1 * s.ω d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / s.ω (d1.gcd d2) := by ring
      rw [cast_ne_zero]; apply ne_zero_of_dvd_ne_zero _ (Nat.gcd_dvd_left d1 d2)
      simp only [Nat.mem_divisors] at hd1P ; exact ne_zero_of_dvd_ne_zero hd1P.right hd1P.left 



--#exit

theorem lambda_sq_mainSum_eq_diag_quad_form (s : Sieve) (w : ℕ → ℝ) :
    s.mainSum (lambdaSquaredOfWeights w) =
      ∑ l in s.P.divisors,
        1 / s.g l * (∑ d in s.P.divisors, if l ∣ d then s.ω d / d * w d else 0) ^ 2 :=
  by
  rw [s.lambda_sq_mainSum_eq_quad_form w]
  calc
    ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
          s.ω d1 / ↑d1 * w d1 * s.ω d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / s.ω (d1.gcd d2) =
        ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
          ↑(d1.gcd d2) / s.ω (d1.gcd d2) * (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      ring
    _ =
        ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
          (∑ l in s.P.divisors, if l ∣ d1.gcd d2 then 1 / s.g l else 0) * (s.ω d1 / ↑d1 * w d1) *
            (s.ω d2 / ↑d2 * w d2) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      rw [mem_divisors] at hd1 hd2 
      rw [s.omega_eq_conv_rec_g (d1.gcd d2) (dvd_trans (Nat.gcd_dvd_left d1 d2) hd1.left)]
    _ = ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors, (∑ l in s.P.divisors,
          if l ∣ d1.gcd d2 then 1 / s.g l * (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) else 0) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      rw [sum_mul]; rw [sum_mul]
      apply sum_congr rfl; intro l hl
      rw [← ite_mul_zero_left]; rw [← ite_mul_zero_left]
    _ = ∑ l in s.P.divisors, ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
          if l ∣ d1 ∧ l ∣ d2 then 1 / s.g l * (s.ω d1 / ↑d1 * w d1) * (s.ω d2 / ↑d2 * w d2) else 0 :=
      by
      apply symm
      rw [sum_comm, sum_congr rfl]; intro d1 hd1
      rw [sum_comm];
      apply sum_congr rfl; intro d2 hd2
      apply sum_congr rfl; intro l hl
      apply ite_eq_of_iff_eq
      apply Iff.symm
      exact Nat.dvd_gcd_iff
      exact fun _ => rfl
    _ =
        ∑ l in s.P.divisors,
          1 / s.g l *
            ∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
              if l ∣ d1 ∧ l ∣ d2 then s.ω d1 / ↑d1 * w d1 * (s.ω d2 / ↑d2 * w d2) else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [mul_sum]; apply sum_congr rfl; intro d1 hd1
      rw [mul_sum]; apply sum_congr rfl; intro d2 hd2
      rw [← ite_mul_zero_right]; rw [mul_assoc]
    _ =
        ∑ l in s.P.divisors,
          1 / s.g l * (∑ d in s.P.divisors, if l ∣ d then s.ω d / ↑d * w d else 0) ^ 2 :=
      by
      apply sum_congr rfl; intro l hl
      suffices :
        (∑ d1 in s.P.divisors, ∑ d2 in s.P.divisors,
            if l ∣ d1 ∧ l ∣ d2 then s.ω d1 / ↑d1 * w d1 * (s.ω d2 / ↑d2 * w d2) else 0) =
          (∑ d in s.P.divisors, if l ∣ d then s.ω d / ↑d * w d else 0) ^ 2
      rw [this, cast_one]
      rw [sq]
      rw [mul_sum]; apply sum_congr rfl; intro d1 hd1
      rw [sum_mul]; apply sum_congr rfl; intro d2 hd2
      rw [ite_and_mul_zero]; ring

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (d1 d2) -/
theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    UpperMoebius <| lambdaSquaredOfWeights weights :=
  by
  dsimp [UpperMoebius, lambdaSquaredOfWeights]
  intro n
  have h_sq :
    (∑ d in n.divisors,
        ∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d in n.divisors, weights d) ^ 2 :=
    by
    rw [sq]
    rw [mul_sum]
    rw [conv_lambda_sq_larger_sum weights n]
    rw [sum_comm]
    apply sum_congr rfl
    intro d1 hd1
    rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro d2 hd2
    rw [← sum_filter fun a : ℕ => a = d1.lcm d2]
    rw [sum_eq_single (d1.lcm d2)]
    · ring
    · intro b hb_in hb_neq
      simp at hb_in 
      exfalso
      cases' hb_in with hb_div hb_eq
      exact hb_neq hb_eq
    · intro h_lcm
      simp at h_lcm hd1 hd2 
      cases' hd1 with hd1 hn1
      cases' hd2 with hd2 hn2
      have hn' : n = 0 := h_lcm (Nat.lcm_dvd hd1 hd2)
      contradiction
  rw [h_sq]
  by_cases hn : n = 1
  · rw [if_pos hn]
    have : ∑ d in n.divisors, weights d = weights 1 :=
      by
      apply sum_eq_single 1
      · intro b hb_dvd hb_none
        exfalso
        rw [hn] at hb_dvd 
        simp at hb_dvd 
        exact hb_none hb_dvd
      · intro h
        simp at h 
        rw [h] at hn 
        contradiction
    rw [this]
    rw [hw]
    linarith
  · rw [if_neg hn]
    apply sq_nonneg

end Sieve

