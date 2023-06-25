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
import SelbergSieve.SieveDef

noncomputable section

open scoped BigOperators Classical Nat.ArithmeticFunction

open Finset Real Nat Aux

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

set_option profiler true

namespace Sieve

set_option quotPrecheck false
variable (s : Sieve)
local notation "ν" => s.nu
local notation "P" => s.prodPrimes
local notation "a" => s.weights
local notation "X" => s.totalMass
local notation "R" => s.rem
local notation "g" => s.selbergTerms

theorem prodPrimes_ne_zero : P ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : Squarefree d :=
  by
  simp only [Nat.mem_divisors, Ne.def] at hd 
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hl : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p in d.factors.toFinset, ν p :=
      by
      apply prod_pos
      intro p hpd; rw [List.mem_toFinset] at hpd 
      have hp_prime : p.Prime := prime_of_mem_factors hpd
      have hp_dvd : p ∣ P := dvd_trans (dvd_of_mem_factors hpd) hl
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := prod_factors_of_mult ν s.nu_mult (Squarefree.squarefree_of_dvd hl s.prodPrimes_squarefree)

theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 :=
  by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd 
  apply s.nu_pos_of_dvd_prodPrimes hd.left
  
theorem multSum_eq_main_err (d : ℕ) : s.multSum d = (ν d) / (d:ℝ) * X + R d :=
  by
  dsimp [rem]
  ring

def delta (n : ℕ) : ℝ := if n=1 then 1 else 0

scoped[Sieve] notation "δ" => delta

theorem siftedSum_as_delta : s.siftedSum = ∑ d in s.support, a d * δ (Nat.gcd P d) :=
  by
  dsimp only [siftedSum]
  apply sum_congr rfl
  intro d hd
  dsimp only [Nat.coprime, delta] at *
  by_cases h : Nat.gcd P d = 1
  · rw [if_pos h]
    rw [if_pos h]
    ring
  · rw [if_neg h]
    rw [if_neg h]
    ring

-- Unused ?
theorem nu_lt_self_of_dvd_prodPrimes : ∀ d : ℕ, d ∣ P → d ≠ 1 → ν d < d :=
  by
  intro d hdP hd_ne_one
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  calc
    ν d = ∏ p in d.factors.toFinset, ν p :=
      eq_comm.mp (prod_factors_of_mult ν s.nu_mult hd_sq)
    _ < ∏ p in d.factors.toFinset, ↑p :=
      by
      have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
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

theorem nu_div_self_ne_zero {d : ℕ} (hd : d ∣ P) : ν d / ↑d ≠ 0 := by
  rw [div_ne_zero_iff]
  constructor
  · exact _root_.ne_of_gt $ s.nu_pos_of_dvd_prodPrimes hd
  · rw [Nat.cast_ne_zero]
    exact ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd

-- S = ∑_{l|P, l≤√y} g(l)
-- Facts about g
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l :=
  by
  have hl_sq : Squarefree l := Squarefree.squarefree_of_dvd hl s.prodPrimes_squarefree
  dsimp only [selbergTerms]
  apply mul_pos
  apply div_pos
  apply lt_of_le_of_ne
  apply le_of_lt
  exact s.nu_pos_of_dvd_prodPrimes hl
  apply ne_comm.mp; apply _root_.ne_of_gt; exact s.nu_pos_of_dvd_prodPrimes hl
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

theorem selbergTerms_mult : Multiplicative g :=
  by
  have : g = (fun d => ν d / ↑d) * fun d => ∏ p in d.factors.toFinset, 1 / (1 - ν p / p) :=
    by ext d; rfl
  rw [this]
  apply mult_mul_of_mult
  exact s.nu_div_self_mult
  exact mult_prod_factors _

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d in l.divisors, (μ <| l / d) * (d / ν d) :=
  by
  dsimp only [selbergTerms]
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

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (d : ℝ) / ν d = ∑ l in divisors P, if l ∣ d then 1 / g l else 0 :=
  by
  apply symm
  rw [← sum_over_dvd_ite s.prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero $ ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
  revert hdP; revert d
  rw [ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on_prop _ (fun _ _ => Nat.dvd_trans)]
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (y / ν y)) (n:=l)]
  apply symm
  exact s.one_div_selbergTerms_eq_conv_moebius_nu l 
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt $ s.nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_self_div_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l in divisors P, if l ∣ d then g l else 0) = g d * (↑d / ν d) := by
  calc
    (∑ l in divisors P, if l ∣ d then g l else 0) =
        ∑ l in divisors P, if l ∣ d then g (d / l) else 0 :=
      by
      rw [← sum_over_dvd_ite s.prodPrimes_ne_zero hd]
      rw [← Nat.sum_divisorsAntidiagonal fun x y => g x]
      rw [Nat.sum_divisorsAntidiagonal' fun x y => g x]
      rw [sum_over_dvd_ite s.prodPrimes_ne_zero hd]
    _ = g d * ∑ l in divisors P, if l ∣ d then 1 / g l else 0 :=
      by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [← ite_mul_zero_right]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← div_mult_of_dvd_squarefree g s.selbergTerms_mult d l]; ring
      exact h; apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      apply _root_.ne_of_gt; rw [mem_divisors] at hl ; apply selbergTerms_pos; exact hl.left
    _ = g d * (↑d / ν d) := by rw [← s.nu_eq_conv_one_div_selbergTerms d hd]


theorem upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
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
      apply sum_over_dvd s.prodPrimes_ne_zero (gcd_dvd P n).left
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

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus :=
  by
  dsimp only [mainSum, errSum]
  have err_bound :
    ∑ d in divisors P, μPlus d * R d ≤ ∑ d in divisors P, |μPlus d| * |R d| := by
    calc
      ∑ d in divisors P, μPlus d * R d ≤ |∑ d in divisors P, μPlus d * R d| :=
        le_abs.mpr (Or.intro_left _ le_rfl)
      _ ≤ ∑ d in divisors P, |μPlus d * R d| :=
        (abs_sum_le_sum_abs (fun d => μPlus d * R d) <| divisors P)
      _ = ∑ d in divisors P, |μPlus d| * |R d| :=
        by
        apply sum_congr rfl; intro d hdP
        exact abs_mul (μPlus d) (R d)
  calc
    s.siftedSum ≤ ∑ d in divisors P, μPlus d * s.multSum d :=
      s.upper_bound_of_UpperBoundSieve μPlus
    _ = ∑ d in divisors P, μPlus d * (ν d / d * X + R d) :=
      by
      apply sum_congr rfl; intro d hdP
      rw [s.multSum_eq_main_err]
    _ = ∑ d in divisors P, (μPlus d * (ν d / d) * X + μPlus d * R d) := by
      apply sum_congr rfl; intro d hdP; ring
    _ = ∑ d in divisors P, μPlus d * (ν d / d) * X + ∑ d in divisors P, μPlus d * R d :=
      sum_add_distrib
    _ = X * ∑ d in divisors P, μPlus d * (ν d / ↑d) + ∑ d in divisors P, μPlus d * R d :=
      by rw [← sum_mul]; rw [mul_comm]
    _ ≤
        X * ∑ d in divisors P, μPlus d * (ν d / ↑d) +
          ∑ d in divisors P, |μPlus d| * |R d| :=
      by linarith

--TODO everything after this could go to a different file, as it relates sieves and lambda squared sieves
theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquaredOfWeights w) =
      ∑ d1 in divisors P, ∑ d2 in divisors P,
        ν d1 / d1 * w d1 * (ν d2 / d2) * w d2 * (d1.gcd d2 / ν (d1.gcd d2)) :=
  by
  dsimp only [mainSum, lambdaSquaredOfWeights]
  trans (∑ d in divisors P, ∑ d1 in divisors d, ∑ d2 in divisors d, 
          if d = d1.lcm d2 then w d1 * w d2 * (ν d / ↑d) else 0)
  · rw [sum_congr rfl]; intro d hd
    rw [sum_mul, sum_congr rfl]; intro d1 hd1
    rw [sum_mul, sum_congr rfl]; intro d2 hd2
    rw [←ite_mul_zero_left]
  
  trans (∑ d in divisors P, ∑ d1 in divisors P, ∑ d2 in divisors P, 
          if d = d1.lcm d2 then w d1 * w d2 * (ν d / ↑d) else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2 
  have h : d1.lcm d2 ∣ P := Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩ 
  rw [←sum_intro' (divisors P) (d1.lcm d2) (mem_divisors.mpr ⟨h, s.prodPrimes_ne_zero⟩ )]  
  rw [mult_lcm_eq_of_ne_zero (fun d => ν d / d) s.nu_div_self_mult _ _ _ 
      (s.squarefree_of_mem_divisors_prodPrimes hd1) (s.squarefree_of_mem_divisors_prodPrimes hd2)]
  rw [div_div_eq_mul_div]
  ring
  apply (s.nu_div_self_ne_zero)
  trans d1
  · exact Nat.gcd_dvd_left d1 d2
  · exact dvd_of_mem_divisors hd1

theorem lambdaSquared_mainSum_eq_diag_quad_form  (w : ℕ → ℝ) :
    s.mainSum (lambdaSquaredOfWeights w) =
      ∑ l in divisors P,
        1 / g l * (∑ d in divisors P, if l ∣ d then ν d / d * w d else 0) ^ 2 :=
  by
  rw [s.lambdaSquared_mainSum_eq_quad_form w]
  calc
    ∑ d1 in divisors P, ∑ d2 in divisors P,
          ν d1 / ↑d1 * w d1 * (ν d2 / ↑d2) * w d2 * (↑(d1.gcd d2) / ν (d1.gcd d2)) =
        ∑ d1 in divisors P, ∑ d2 in divisors P,
          ↑(d1.gcd d2) / ν (d1.gcd d2) * (ν d1 / ↑d1 * w d1) * (ν d2 / ↑d2 * w d2) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      ring
    _ =
        ∑ d1 in divisors P, ∑ d2 in divisors P,
          (∑ l in divisors P, if l ∣ d1.gcd d2 then 1 / g l else 0) * (ν d1 / ↑d1 * w d1) *
            (ν d2 / ↑d2 * w d2) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      rw [mem_divisors] at hd1 hd2 
      rw [s.nu_eq_conv_one_div_selbergTerms (d1.gcd d2) (dvd_trans (Nat.gcd_dvd_left d1 d2) hd1.left)]
    _ = ∑ d1 in divisors P, ∑ d2 in divisors P, (∑ l in divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 / ↑d1 * w d1) * (ν d2 / ↑d2 * w d2) else 0) :=
      by
      apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 hd2
      rw [sum_mul]; rw [sum_mul]
      apply sum_congr rfl; intro l hl
      rw [← ite_mul_zero_left]; rw [← ite_mul_zero_left]
    _ = ∑ l in divisors P, ∑ d1 in divisors P, ∑ d2 in divisors P,
          if l ∣ d1 ∧ l ∣ d2 then 1 / g l * (ν d1 / ↑d1 * w d1) * (ν d2 / ↑d2 * w d2) else 0 :=
      by
      apply symm
      rw [sum_comm, sum_congr rfl]; intro d1 hd1
      rw [sum_comm];
      apply sum_congr rfl; intro d2 hd2
      apply sum_congr rfl; intro l hl
      apply if_ctx_congr _ _ (fun _ => rfl)
      apply Iff.symm
      exact Nat.dvd_gcd_iff
      exact fun _ => rfl
    _ =
        ∑ l in divisors P,
          1 / g l *
            ∑ d1 in divisors P, ∑ d2 in divisors P,
              if l ∣ d1 ∧ l ∣ d2 then ν d1 / ↑d1 * w d1 * (ν d2 / ↑d2 * w d2) else 0 :=
      by
      apply sum_congr rfl; intro l hl
      rw [mul_sum]; apply sum_congr rfl; intro d1 hd1
      rw [mul_sum]; apply sum_congr rfl; intro d2 hd2
      rw [← ite_mul_zero_right]; rw [mul_assoc]
    _ =
        ∑ l in divisors P,
          1 / g l * (∑ d in divisors P, if l ∣ d then ν d / ↑d * w d else 0) ^ 2 :=
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

