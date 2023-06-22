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
import SelbergSieve.LambdaSquaredDef

noncomputable section

open scoped BigOperators Classical Nat.ArithmeticFunction

open Finset Real Nat Aux

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option profiler -/
set_option profiler true


structure Sieve where mk ::
  support : Finset ℕ
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  weights : ℕ → ℝ
  ha_nonneg : ∀ n : ℕ, 0 ≤ weights n
  totalMass : ℝ
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ P → 0 < nu p
  nu_lt_self_of_prime : ∀ p : ℕ, p.Prime → p ∣ P → nu p < p

namespace Sieve

set_option quotPrecheck false
variable (s : Sieve)
scoped[Sieve] notation "ν" => s.nu
scoped[Sieve] notation "P" => s.prodPrimes
scoped[Sieve] notation "a" => s.weights
scoped[Sieve] notation "X" => s.totalMass

theorem hP_ne_zero : P ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree

theorem sqfree_of_dvd_P {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
theorem sqfree_of_mem_dvd_P {d : ℕ} (hd : d ∈ divisors P) : Squarefree d :=
  by
  simp only [Nat.mem_divisors, Ne.def] at hd 
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

theorem nu_pos_of_dvd_P {d : ℕ} (hl : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p in d.factors.toFinset, ν p :=
      by
      apply prod_pos
      intro p hpd; rw [List.mem_toFinset] at hpd 
      have hp_prime : p.Prime := prime_of_mem_factors hpd
      have hp_dvd : p ∣ P := dvd_trans (dvd_of_mem_factors hpd) hl
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := prod_factors_of_mult ν s.nu_mult (Squarefree.squarefree_of_dvd hl s.prodPrimes_squarefree)

theorem nu_ne_zero_of_mem_dvd_P {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 :=
  by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd 
  apply s.nu_pos_of_dvd_P hd.left

@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n in s.support, if d ∣ n then a n else 0

-- A_d = ν (d)/d X + R_d
@[simp]
def R (d : ℕ) : ℝ :=
  s.multSum d - ν d / d * X

theorem multSum_eq_main_err (d : ℕ) : s.multSum d = (ν d) / (d:ℝ) * X + s.R d :=
  by
  dsimp [R]
  ring

def siftedSum : ℝ :=
  ∑ d in s.support, if coprime P d then a d else 0

@[simp]
def δ (n : ℕ) : ℝ :=
  if n = 1 then 1 else 0

theorem siftedSum_as_delta : s.siftedSum = ∑ d in s.support, a d * δ (Nat.gcd P d) :=
  by
  --cases' s with A P hP a ha_pos X nu
  dsimp only [siftedSum]
  apply sum_congr rfl
  intro d hd
  dsimp only [Nat.coprime, δ] at *
  by_cases h : Nat.gcd P d = 1
  · rw [if_pos h]
    rw [if_pos h]
    ring
  · rw [if_neg h]
    rw [if_neg h]
    ring

def nu_lt_self_of_dvd_P : ∀ d : ℕ, d ∣ P → d ≠ 1 → ν d < d :=
  by
  intro d hdP hd_ne_one
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  calc
    ν d = ∏ p in d.factors.toFinset, ν p :=
      eq_comm.mp (prod_factors_of_mult ν s.nu_mult hd_sq)
    _ < ∏ p in d.factors.toFinset, ↑p :=
      by
      have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero s.hP_ne_zero hdP
      apply prod_le_prod_of_nonempty
      · intro p hp; rw [List.mem_toFinset] at hp 
        rw [mem_factors hd_ne_zero] at hp 
        apply s.nu_pos_of_prime p hp.left (dvd_trans hp.right hdP)
      · intro p hpd; rw [List.mem_toFinset] at hpd ; rw [mem_factors hd_ne_zero] at hpd 
        apply s.nu_lt_self_of_prime p hpd.left (dvd_trans hpd.right hdP)
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
      

theorem nu_div_self_mult : Multiplicative (fun d => ν d / ↑d) :=
  by
  apply div_mult_of_mult
  exact s.nu_mult
  exact coe_mult
  intro n hn
  rw [Nat.cast_ne_zero]
  exact _root_.ne_of_gt hn


-- Used in statement of the simple form of the selberg bound
def g (d : ℕ) : ℝ :=
  ν d / d * ∏ p in d.factors.toFinset, 1 / (1 - ν p / p)

-- S = ∑_{l|P, l≤√y} g(l)
-- Facts about g
theorem hg_pos (l : ℕ) (hl : l ∣ P) : 0 < s.g l :=
  by
  have hl_sq : Squarefree l := Squarefree.squarefree_of_dvd hl s.prodPrimes_squarefree
  dsimp only [g]
  apply mul_pos
  apply div_pos
  apply lt_of_le_of_ne
  apply le_of_lt
  exact s.nu_pos_of_dvd_P hl
  apply ne_comm.mp; apply _root_.ne_of_gt; exact s.nu_pos_of_dvd_P hl
  suffices : 0 < l; exact cast_pos.mpr this
  rw [zero_lt_iff]; exact Squarefree.ne_zero hl_sq
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  rw [List.mem_toFinset] at hp 
  have hp_prime : p.Prime := prime_of_mem_factors hp
  have hp_dvd : p ∣ P := by
    calc
      p ∣ l := Nat.dvd_of_mem_factors hp
      _ ∣ P := hl
  have : ν p < p := s.nu_lt_self_of_prime p hp_prime hp_dvd
  have hp_pos : 0 < (p : ℝ) :=
    by
    suffices 0 < p by exact cast_pos.mpr this
    exact Nat.Prime.pos hp_prime
  have hp_ne_zero : (p : ℝ) ≠ 0 := ne_comm.mp (ne_of_lt hp_pos)
  rw [← zero_lt_mul_right hp_pos]
  calc
    0 < ↑p - ν p := by linarith only [this]
    _ = (1 - ν p / ↑p) * ↑p := by
      conv =>
        lhs
        rw [← (div_mul_cancel (ν p) hp_ne_zero : ν p / p * p = ν p)];
      ring

theorem hg_mult : Multiplicative s.g :=
  by
  have : s.g = (fun d => ν d / ↑d) * fun d => ∏ p in d.factors.toFinset, 1 / (1 - ν p / p) :=
    by ext d; rfl
  rw [this]
  apply mult_mul_of_mult
  exact s.nu_div_self_mult
  exact mult_prod_factors _

theorem rec_g_eq_conv_moebius_omega (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / s.g l = ∑ d in l.divisors, (μ <| l / d) * (d / ν d) :=
  by
  dsimp only [g]
  simp only [one_div, mul_inv, inv_div, inv_inv, Finset.prod_congr, Finset.prod_inv_distrib]
  rw [prod_eq_moebius_sum fun d => ν d / (d : ℝ)]
  · rw [mul_sum]
    calc
      ∑ d in l.divisors, ↑l / ν l * (↑(μ d) * (ν d / ↑d)) =
          ∑ d in l.divisors, ↑(μ d) * (↑l / ↑d) * (ν d / ν l) :=
        by apply sum_congr rfl; intro d hd; ring
      _ = ∑ d in l.divisors, ↑(μ d) * ↑(l / d) * (1 / (ν l / ν d)) :=
        by
        apply sum_congr rfl; intro d hd
        rw [mem_divisors] at hd 
        rw [← Nat.cast_div hd.left]
        rw [one_div_div]
        rw [Nat.cast_ne_zero]
        exact ne_zero_of_dvd_ne_zero hd.right hd.left
      _ = ∑ d in l.divisors, ↑(μ d) * (↑(l / d) / ν (l / d)) :=
        by
        apply sum_congr rfl; intro d hd
        rw [mem_divisors] at hd 
        rw [div_mult_of_dvd_squarefree ν s.nu_mult l d hd.left hl]
        ring
        revert hnu_nonzero; contrapose!
        exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd.left
      _ = l.divisors.sum fun d => ↑(μ d) * (↑(l / d) / ν (l / d)) := rfl
      _ = l.divisors.sum fun d => μ (l / d) * (↑d / ν d) :=
        by
        rw [← Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (↑e / ν e)]
        rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (↑e / ν e)]
  exact s.nu_div_self_mult
  exact hl

theorem omega_eq_conv_rec_g (d : ℕ) (hdP : d ∣ P) :
    (d : ℝ) / ν d = ∑ l in divisors P, if l ∣ d then 1 / s.g l else 0 :=
  by
  -- Problem, these identities only hold on l ∣ P, so can't use standard moebius inversion results,
  rw [eq_comm]
  calc
    (∑ l in divisors P, if l ∣ d then 1 / s.g l else 0) =
        ∑ l in divisors P, if l ∣ d then ∑ k in l.divisors, (μ <| l / k) * (k / ν k) else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [s.rec_g_eq_conv_moebius_omega l (s.sqfree_of_mem_dvd_P hl) (s.nu_ne_zero_of_mem_dvd_P hl)]
    _ =
        ∑ l in divisors P,
          if l ∣ d then ∑ k in divisors P, if k ∣ l then (μ <| l / k) * (k / ν k) else 0
          else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [mem_divisors] at hl ; rw [← sum_over_dvd_ite s.hP_ne_zero hl.left]
    _ =
        ∑ l in divisors P,
          (∑ k in divisors P, if k ∣ l then (μ <| l / k) * (k / ν k) else 0) *
            if l ∣ d then 1 else 0 :=
      by
      conv =>
        rhs
        congr
        . skip
        . ext
          rw [mul_boole]
    _ =
        ∑ l in divisors P, ∑ k in divisors P, 
          (if k ∣ l then (μ <| l / k) * (k / ν k) else 0) * if l ∣ d then 1 else 0 :=
      by apply sum_congr rfl; intro l hl; rw [sum_mul]
    _ = ∑ k in divisors P, ∑ l in divisors P, (if k ∣ l ∧ l ∣ d then (μ <| l / k) * (k / ν k) else 0) :=
      by
      rw [sum_comm]
      apply sum_congr rfl; intro l hl
      apply sum_congr rfl; intro k hk
      rw [← ite_and_mul_zero]
      apply ite_eq_of_iff_eq _ _ Iff.rfl; intro; ring
    _ = ∑ k in divisors P, ∑ l in divisors P, (if k ∣ l ∧ l ∣ d then (μ l:ℝ) / (μ k:ℝ) else 0) * (k / ν k) :=
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
        ∑ k in divisors P,
          (∑ l in divisors P, if k ∣ l ∧ l ∣ d then (μ l:ℝ) else 0) / (μ k:ℝ) * (k / ν k) :=
      by
      apply sum_congr rfl; intro k hk
      conv =>
        lhs
        congr
        . skip
        . ext
          rw [div_eq_mul_inv, ite_mul_zero_left]
      rw [← sum_mul, ← sum_mul, ← div_eq_mul_inv]
    _ = ∑ k in divisors P, (if k = d then (μ k:ℝ) else 0) / (μ k:ℝ) * (k / ν k) :=
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
      rw [moebius_inv_dvd_lower_bound s.prodPrimes_squarefree k d hdP]
      rw [← Int.cast_ite]
    _ = ↑d / ν d := by
      rw [Finset.sum_eq_single d]
      rw [if_pos rfl]; rw [div_self]; ring
      rw [Int.cast_ne_zero]
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      intro k hk hkd; rw [if_neg hkd]; ring
      intro hd; rw [mem_divisors] at hd 
      exfalso; push_neg at hd 
      exact s.hP_ne_zero (hd hdP)

theorem conv_g_eq {d : ℕ} (hd : d ∣ P) :
    (∑ l in divisors P, if l ∣ d then s.g l else 0) = s.g d * (↑d / ν d) := by
  calc
    (∑ l in divisors P, if l ∣ d then s.g l else 0) =
        ∑ l in divisors P, if l ∣ d then s.g (d / l) else 0 :=
      by
      rw [← sum_over_dvd_ite s.hP_ne_zero hd]
      rw [← Nat.sum_divisorsAntidiagonal fun x y => s.g x]
      rw [Nat.sum_divisorsAntidiagonal' fun x y => s.g x]
      rw [sum_over_dvd_ite s.hP_ne_zero hd]
    _ = s.g d * ∑ l in divisors P, if l ∣ d then 1 / s.g l else 0 :=
      by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [← ite_mul_zero_right]; apply ite_eq_of_iff_eq _ _ Iff.rfl; intro h
      rw [← div_mult_of_dvd_squarefree s.g s.hg_mult d l]; ring
      exact h.left; apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      apply _root_.ne_of_gt; rw [mem_divisors] at hl ; apply hg_pos; exact hl.left
    _ = s.g d * (↑d / ν d) := by rw [← s.omega_eq_conv_rec_g d hd]


def mainSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d in divisors P, μPlus d * ν d / d

def errSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d in divisors P, |μPlus d| * |s.R d|

theorem upper_bound_of_upperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ ∑ d in divisors P, μPlus d * s.multSum d :=
  by
  have hμ : ∀ n, δ n ≤ ∑ d in n.divisors, μPlus d := μPlus.hμPlus
  rw [siftedSum_as_delta]
  calc
    ∑ n in s.support, a n * δ (Nat.gcd P n) ≤ ∑ n in s.support, a n * ∑ d in (Nat.gcd P n).divisors, μPlus d :=
      by
      apply Finset.sum_le_sum
      intro n hnA
      exact mul_le_mul_of_nonneg_left (hμ (Nat.gcd P n)) (s.ha_nonneg n)
    _ = ∑ n in s.support, ∑ d in (Nat.gcd P n).divisors, a n * μPlus d :=
      by
      apply sum_congr rfl; intro n hnA
      exact mul_sum
    _ = ∑ n in s.support, ∑ d in divisors P, if d ∣ n then a n * μPlus d else 0 :=
      by
      apply sum_congr rfl; intro n hnA
      apply sum_over_dvd s.hP_ne_zero (gcd_dvd P n).left
      · intro d hd
        have : ¬d ∣ n := by
          by_contra h
          exact hd.right (Nat.dvd_gcd_iff.mpr ⟨hd.left, h⟩)
        exact if_neg this
      · intro d hd
        have : d ∣ n := dvd_trans hd (gcd_dvd P n).right
        exact if_pos this
    _ = ∑ d in divisors P, ∑ n in s.support, if d ∣ n then a n * μPlus d else 0 := Finset.sum_comm
    _ = ∑ d in divisors P, ∑ n in s.support, μPlus d * if d ∣ n then a n else 0 :=
      by
      apply sum_congr rfl; intro d hdP
      apply sum_congr rfl; intro n hnA
      rw [ite_mul_zero_left]; ring
    _ = ∑ d in divisors P, μPlus d * ∑ n in s.support, if d ∣ n then a n else 0 :=
      by
      apply sum_congr rfl; intro d hdP
      rw [eq_comm]
      apply mul_sum

theorem upper_bound_main_err (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus :=
  by
  dsimp only [mainSum, errSum]
  have err_bound :
    ∑ d in divisors P, μPlus d * s.R d ≤ ∑ d in divisors P, |μPlus d| * |s.R d| := by
    calc
      ∑ d in divisors P, μPlus d * s.R d ≤ |∑ d in divisors P, μPlus d * s.R d| :=
        le_abs.mpr (Or.intro_left _ le_rfl)
      _ ≤ ∑ d in divisors P, |μPlus d * s.R d| :=
        (abs_sum_le_sum_abs (fun d => μPlus d * s.R d) <| divisors P)
      _ = ∑ d in divisors P, |μPlus d| * |s.R d| :=
        by
        apply sum_congr rfl; intro d hdP
        exact abs_mul (μPlus d) (s.R d)
  calc
    s.siftedSum ≤ ∑ d in divisors P, μPlus d * s.multSum d :=
      s.upper_bound_of_upperBoundSieve μPlus
    _ = ∑ d in divisors P, μPlus d * (ν d / d * X + s.R d) :=
      by
      apply sum_congr rfl; intro d hdP
      rw [s.multSum_eq_main_err]
    _ = ∑ d in divisors P, (μPlus d * ν d / d * X + μPlus d * s.R d) := by
      apply sum_congr rfl; intro d hdP; ring
    _ = ∑ d in divisors P, μPlus d * ν d / d * X + ∑ d in divisors P, μPlus d * s.R d :=
      sum_add_distrib
    _ = X * ∑ d in divisors P, μPlus d * ν d / ↑d + ∑ d in divisors P, μPlus d * s.R d :=
      by rw [← sum_mul]; rw [mul_comm]
    _ ≤
        X * ∑ d in divisors P, μPlus d * ν d / ↑d +
          ∑ d in divisors P, |μPlus d| * |s.R d| :=
      by linarith

--TODO everything after this could go to a different file, as it relates sieves and lambda squared sieves

theorem lambda_sq_mainSum_eq_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquaredOfWeights w) =
      ∑ d1 in divisors P, ∑ d2 in divisors P,
        ν d1 / d1 * w d1 * ν d2 / d2 * w d2 * d1.gcd d2 / ν (d1.gcd d2) :=
  by
  dsimp only [mainSum, lambdaSquaredOfWeights]
  calc
    ∑ d in divisors P,
          (∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = d1.lcm d2 then w d1 * w d2 else 0) * ν d / ↑d =
        ∑ d in divisors P,
          (∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = d1.lcm d2 then w d1 * w d2 else 0) * (ν d / ↑d) :=
      by apply sum_congr rfl; intro d hdP; ring
    _ =
        ∑ d in divisors P, ∑ d1 in d.divisors, ∑ d2 in d.divisors, 
          (if d = d1.lcm d2 then w d1 * w d2 else 0) * (ν d / ↑d) :=
      by apply sum_congr rfl; intro d hdP; rw [sum_mul]; apply sum_congr rfl; intro d1 hd1d; rw [sum_mul]
    _ =
        ∑ d in divisors P, ∑ d1 in d.divisors, ∑ d2 in d.divisors, 
          if d = d1.lcm d2 then w d1 * w d2 * ν d / ↑d else 0 :=
      by 
      apply sum_congr rfl; intro d hdP; apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl;
      intro d2 hd2
      rw [← ite_mul_zero_left]
      apply ite_eq_of_iff_eq _ _ Iff.rfl
      rintro ⟨h, _⟩; ring 
    _ =
        ∑ d in divisors P, ∑ d1 in divisors P, ∑ d2 in d.divisors, 
          if d = d1.lcm d2 then w d1 * w d2 * ν d / ↑d else 0 :=
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
    _ = ∑ d in divisors P, ∑ d1 in divisors P, ∑ d2 in divisors P, 
          if d = d1.lcm d2 then w d1 * w d2 * ν d / ↑d else 0 :=
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
    _ = ∑ d1 in divisors P, ∑ d2 in divisors P, ∑ d in divisors P,  if d = d1.lcm d2 then w d1 * w d2 * ν d / ↑d else 0 := 
      by rw [sum_comm]; apply sum_congr rfl; intro d1 hd1; rw [sum_comm]
    _ =
        ∑ d1 in divisors P, ∑ d2 in divisors P, ∑ d in divisors P, 
          if d = d1.lcm d2 ∧ True then w d1 * w d2 * ν (d1.lcm d2) / ↑(d1.lcm d2) else 0 :=
      by 
      apply sum_congr rfl; intro d1 hd1P; apply sum_congr rfl; intro d2 hd2; apply sum_congr rfl;
      intro d hd
      apply ite_eq_of_iff_eq
      · rw [and_true_iff]
      rintro ⟨h, _⟩; rw [← h]
    _ =
        ∑ d1 in divisors P, ∑ d2 in divisors P,
          if True then w d1 * w d2 * ν (d1.lcm d2) / ↑(d1.lcm d2) else 0 :=
      by 
      apply sum_congr rfl; intro d1 hd1P; apply sum_congr rfl; intro d2 hd2P
      rw [← sum_intro (divisors P) True (w d1 * w d2 * ν (d1.lcm d2) / ↑(d1.lcm d2))]
      rw [mem_divisors] at hd1P hd2P 
      intro
      rw [mem_divisors]; constructor
      exact Nat.lcm_dvd_iff.mpr ⟨hd1P.left, hd2P.left⟩
      exact hd1P.right
    _ = ∑ d1 in divisors P, ∑ d2 in divisors P, 
          w d1 * w d2 * ν (d1.lcm d2) / ↑(d1.lcm d2) :=
      by 
      apply sum_congr rfl; intro d1 _; apply sum_congr rfl; intro d2 _
      rw [if_pos trivial]
    _ =
        ∑ d1 in divisors P, ∑ d2 in divisors P,
          ν d1 / ↑d1 * w d1 * ν d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / ν (d1.gcd d2) :=
      by 
      apply sum_congr rfl; intro d1 hd1P; apply sum_congr rfl; intro d2 hd2P
      have : ν (d1.lcm d2) = ν d1 * ν d2 / ν (d1.gcd d2) :=
        by
        by_cases h_zero : ν (d1.gcd d2) = 0
        · rw [h_zero]; simp only [div_zero]
          have : d1.gcd d2 ∣ d1.lcm d2
          calc
            d1.gcd d2 ∣ d1 := Nat.gcd_dvd_left d1 d2
            _ ∣ d1.lcm d2 := Nat.dvd_lcm_left d1 d2
          exact
            multiplicative_zero_of_zero_dvd ν s.nu_mult
              (lcm_squarefree_of_squarefree (s.sqfree_of_mem_dvd_P hd1P)
                (s.sqfree_of_mem_dvd_P hd2P))
              this h_zero
        · rw [eq_div_iff_mul_eq h_zero]; rw [eq_comm]
          exact
            mult_gcd_lcm_of_squarefree ν s.nu_mult d1 d2 (s.sqfree_of_mem_dvd_P hd1P)
              (s.sqfree_of_mem_dvd_P hd2P)
      rw [this]
      dsimp only [Nat.lcm]
      rw [Nat.cast_div (Aux.gcd_dvd_mul d1 d2)]
      rw [Nat.cast_mul]
      calc
        w d1 * w d2 * (ν d1 * ν d2 / ν (d1.gcd d2)) / (↑d1 * ↑d2 / ↑(d1.gcd d2)) =
            w d1 * w d2 * ν d1 * ν d2 / ν (d1.gcd d2) / (↑d1 * ↑d2 / ↑(d1.gcd d2)) :=
          by ring
        _ = w d1 * w d2 * ν d1 * ν d2 / ν (d1.gcd d2) / (↑d1 * ↑d2) * ↑(d1.gcd d2) := by
          rw [← div_mul]
        _ = w d1 * w d2 * ν d1 * ν d2 / ν (d1.gcd d2) / ↑d1 / ↑d2 * ↑(d1.gcd d2) := by
          rw [← div_div]
        _ = ν d1 / ↑d1 * w d1 * ν d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / ν (d1.gcd d2) := by ring
      rw [cast_ne_zero]; apply ne_zero_of_dvd_ne_zero _ (Nat.gcd_dvd_left d1 d2)
      simp only [Nat.mem_divisors] at hd1P ; exact ne_zero_of_dvd_ne_zero hd1P.right hd1P.left 


theorem lambda_sq_mainSum_eq_diag_quad_form  (w : ℕ → ℝ) :
    s.mainSum (lambdaSquaredOfWeights w) =
      ∑ l in divisors P,
        1 / s.g l * (∑ d in divisors P, if l ∣ d then ν d / d * w d else 0) ^ 2 :=
  by
  rw [s.lambda_sq_mainSum_eq_quad_form w]
  calc
    ∑ d1 in divisors P, ∑ d2 in divisors P,
          ν d1 / ↑d1 * w d1 * ν d2 / ↑d2 * w d2 * ↑(d1.gcd d2) / ν (d1.gcd d2) =
        ∑ d1 in divisors P, ∑ d2 in divisors P,
          ↑(d1.gcd d2) / ν (d1.gcd d2) * (ν d1 / ↑d1 * w d1) * (ν d2 / ↑d2 * w d2) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      ring
    _ =
        ∑ d1 in divisors P, ∑ d2 in divisors P,
          (∑ l in divisors P, if l ∣ d1.gcd d2 then 1 / s.g l else 0) * (ν d1 / ↑d1 * w d1) *
            (ν d2 / ↑d2 * w d2) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      rw [mem_divisors] at hd1 hd2 
      rw [s.omega_eq_conv_rec_g (d1.gcd d2) (dvd_trans (Nat.gcd_dvd_left d1 d2) hd1.left)]
    _ = ∑ d1 in divisors P, ∑ d2 in divisors P, (∑ l in divisors P,
          if l ∣ d1.gcd d2 then 1 / s.g l * (ν d1 / ↑d1 * w d1) * (ν d2 / ↑d2 * w d2) else 0) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      rw [sum_mul]; rw [sum_mul]
      apply sum_congr rfl; intro l hl
      rw [← ite_mul_zero_left]; rw [← ite_mul_zero_left]
    _ = ∑ l in divisors P, ∑ d1 in divisors P, ∑ d2 in divisors P,
          if l ∣ d1 ∧ l ∣ d2 then 1 / s.g l * (ν d1 / ↑d1 * w d1) * (ν d2 / ↑d2 * w d2) else 0 :=
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
        ∑ l in divisors P,
          1 / s.g l *
            ∑ d1 in divisors P, ∑ d2 in divisors P,
              if l ∣ d1 ∧ l ∣ d2 then ν d1 / ↑d1 * w d1 * (ν d2 / ↑d2 * w d2) else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [mul_sum]; apply sum_congr rfl; intro d1 hd1
      rw [mul_sum]; apply sum_congr rfl; intro d2 hd2
      rw [← ite_mul_zero_right]; rw [mul_assoc]
    _ =
        ∑ l in divisors P,
          1 / s.g l * (∑ d in divisors P, if l ∣ d then ν d / ↑d * w d else 0) ^ 2 :=
      by
      apply sum_congr rfl; intro l hl
      suffices :
        (∑ d1 in divisors P, ∑ d2 in divisors P,
            if l ∣ d1 ∧ l ∣ d2 then ν d1 / ↑d1 * w d1 * (ν d2 / ↑d2 * w d2) else 0) =
          (∑ d in divisors P, if l ∣ d then ν d / ↑d * w d else 0) ^ 2
      rw [this, cast_one]
      rw [sq]
      rw [mul_sum]; apply sum_congr rfl; intro d1 hd1
      rw [sum_mul]; apply sum_congr rfl; intro d2 hd2
      rw [ite_and_mul_zero]; ring


end Sieve

