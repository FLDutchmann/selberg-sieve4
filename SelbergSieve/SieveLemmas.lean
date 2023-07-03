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
import SelbergSieve.AesopDiv
import SelbergSieve.UpperBoundSieve

noncomputable section

open scoped BigOperators Classical Nat.ArithmeticFunction

open Finset Real Nat Aux

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

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

attribute [aesop safe (rule_sets [Divisibility])] Sieve.prodPrimes_squarefree

namespace Sieve



set_option quotPrecheck false
variable (s : Sieve)
local notation "ν" => s.nu
local notation "P" => s.prodPrimes
local notation "a" => s.weights
local notation "X" => s.totalMass

pp_extended_field_notation nu
pp_extended_field_notation prodPrimes
pp_extended_field_notation weights
pp_extended_field_notation totalMass

@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n in s.support, if d ∣ n then a n else 0

-- A_d = ν (d)/d X + R_d
@[simp]
def rem (d : ℕ) : ℝ :=
  s.multSum d - ν d / d * X

local notation "R" => s.rem
pp_extended_field_notation rem

def siftedSum : ℝ :=
  ∑ d in s.support, if coprime P d then a d else 0

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound
def selbergTerms (d : ℕ) : ℝ :=
  ν d / d * ∏ p in d.factors.toFinset, 1 / (1 - ν p / p)

local notation "g" => s.selbergTerms
pp_extended_field_notation selbergTerms

def mainSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d in divisors P, μPlus d * (ν d / d)

def errSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d in divisors P, |μPlus d| * |R d|

section SieveLemmas

@[aesop forward safe (rule_sets [Divisibility])]
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

local notation "δ" => delta

theorem siftedSum_as_delta : s.siftedSum = ∑ d in s.support, a d * δ (Nat.gcd P d) :=
  by
  dsimp only [siftedSum]
  apply sum_congr rfl
  intro d _
  dsimp only [Nat.coprime, delta] at *
  rw [←ite_mul_zero_right]
  exact if_congr Iff.rfl (symm $ mul_one _) rfl

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
      

theorem nu_div_self_mult : Multiplicative (fun d => ν d / ↑d) := by
  apply div_mult_of_mult
  exact s.nu_mult
  exact coe_mult
  intro n hn
  rw [Nat.cast_ne_zero]
  exact _root_.ne_of_gt hn

@[aesop safe]
theorem nu_div_self_pos {d : ℕ} (hd : d ∣ P) : 0 < ν d / ↑d := by
  apply div_pos (s.nu_pos_of_dvd_prodPrimes hd)
  norm_cast; rw [_root_.zero_lt_iff]
  exact ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd

@[aesop safe]
theorem nu_div_self_ne_zero {d : ℕ} (hd : d ∣ P) : ν d / ↑d ≠ 0 := 
  _root_.ne_of_gt (s.nu_div_self_pos hd)

@[aesop safe]
theorem nu_div_self_lt_one_of_prime {p : ℕ} (hp: p.Prime) (hpP : p ∣ P) : 
    ν p / p < 1 := by
  have hp_pos : (0:ℝ) < (p:ℝ) := by
    norm_cast; exact _root_.zero_lt_iff.mpr $ Nat.Prime.ne_zero hp 
  rw [←mul_lt_mul_right hp_pos]
  rw [one_mul, div_mul_cancel _ (_root_.ne_of_gt hp_pos)]
  exact s.nu_lt_self_of_prime p hp hpP

-- Facts about g
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l :=
  by
  dsimp only [selbergTerms]
  apply mul_pos
  exact s.nu_div_self_pos hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  rw [List.mem_toFinset] at hp 
  have hp_prime : p.Prime := prime_of_mem_factors hp
  have hp_dvd : p ∣ P := Trans.trans (Nat.dvd_of_mem_factors hp) hl
  linarith only [s.nu_div_self_lt_one_of_prime hp_prime hp_dvd]

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
  rw [prod_eq_moebius_sum (fun d => ν d / (d : ℝ)) (s.nu_div_self_mult) hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (↑e / ν e)]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (↑e / ν e)]
  apply sum_congr rfl; intro d hd 
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, 
      cast_div (hd_dvd), div_div_eq_mul_div]
  ring
  · norm_cast; exact ne_zero_of_dvd_ne_zero (Squarefree.ne_zero hl) hd_dvd
  revert hnu_nonzero; contrapose!
  exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (d : ℝ) / ν d = ∑ l in divisors P, if l ∣ d then 1 / g l else 0 :=
  by
  apply symm
  rw [← sum_over_dvd_ite s.prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero $ ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
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
        ∑ l in divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite s.prodPrimes_ne_zero hd]
      rw [← Nat.sum_divisorsAntidiagonal fun x _ => g x]
      rw [Nat.sum_divisorsAntidiagonal' fun x _ => g x]
      rw [sum_over_dvd_ite s.prodPrimes_ne_zero hd]
    _ = g d * ∑ l in divisors P, if l ∣ d then 1 / g l else 0 := by
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
  trans (∑ n in s.support, a n * ∑ d in (Nat.gcd P n).divisors, μPlus d)
  · apply Finset.sum_le_sum; intro n _
    exact mul_le_mul_of_nonneg_left (hμ (Nat.gcd P n)) (s.ha_nonneg n)
  apply le_of_eq
  trans (∑ n in s.support, ∑ d in divisors P, if d ∣ n then a n * μPlus d else 0)
  · apply sum_congr rfl; intro n _;
    rw [mul_sum, sum_over_dvd_ite s.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _), sum_congr rfl]; intro d hd
    apply if_congr _ rfl rfl
    rw [Nat.dvd_gcd_iff, and_iff_right (dvd_of_mem_divisors hd)]
  rw [sum_comm, sum_congr rfl]; intro d _
  dsimp only [multSum]
  rw [mul_sum, sum_congr rfl]; intro n _
  rw [ite_mul_zero_left, mul_comm]

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus :=
  by
  dsimp only [mainSum, errSum]
  trans (∑ d in divisors P, μPlus d * s.multSum d)
  · apply upper_bound_of_UpperBoundSieve
  trans ( X * ∑ d in divisors P, μPlus d * (ν d / ↑d) + ∑ d in divisors P, μPlus d * R d )
  · apply le_of_eq
    rw [mul_sum, ←sum_add_distrib]
    apply sum_congr rfl; intro d _
    dsimp only [rem]; ring
  apply _root_.add_le_add (le_rfl)
  apply sum_le_sum; intro d _
  rw [←abs_mul]
  exact le_abs_self (UpperBoundSieve.μPlus μPlus d * rem s d)

end SieveLemmas
end Sieve

namespace Sieve
-- Results about Lambda Squared Sieves
section LambdaSquared

def lambdaSquaredOfWeights (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

theorem lambdaSquaredOfWeights_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬(d : ℝ) ^ 2 ≤ y → w d = 0) (d : ℕ) (hd :¬ ↑d ≤ y) :
    lambdaSquaredOfWeights w d = 0 := by
  dsimp only [lambdaSquaredOfWeights]
  by_cases hy : 0 ≤ y
  swap
  · push_neg at hd hy 
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw; push_neg
      have : (0:ℝ) ≤ (d' : ℝ) ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _ 
    rw [this d1, this d2]
    simp only [ite_self, eq_self_iff_true, MulZeroClass.mul_zero]
  apply sum_eq_zero; intro d1 hd1; apply sum_eq_zero; intro d2 hd2
  by_cases h : d = d1.lcm d2
  swap; rw [if_neg h]
  rw [if_pos h]
  wlog hass : d1 ≤ d2
  · push_neg at hass 
    rw [mul_comm]
    refine' this w y hw d hd hy d2 hd2 d1 hd1 _ (le_of_lt hass)
    rw [Nat.lcm_comm]; exact h
  rw [hw d2 _, MulZeroClass.mul_zero]
  · by_contra hyp
    apply absurd hd; push_neg
    calc _ ≤ (d1.lcm d2:ℝ) := ?_
         _ ≤ (d1:ℝ)*(d2:ℝ) := ?_
         _ ≤ (d2:ℝ)^2      := ?_
         _ ≤ y             := hyp
    · rw [h]
    · norm_cast; apply Nat.div_le_self
    · norm_cast; rw [sq]; apply mul_le_mul hass le_rfl (Nat.zero_le d2) (Nat.zero_le d2)
  
theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    UpperMoebius <| lambdaSquaredOfWeights weights :=
  by
  dsimp [UpperMoebius, lambdaSquaredOfWeights]
  intro n
  have h_sq :
    (∑ d in n.divisors, ∑ d1 in d.divisors, ∑ d2 in d.divisors, 
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d in n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [←Aux.sum_intro']
    ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩ 
  rw [h_sq]
  by_cases hn : n = 1
  · rw [if_pos hn]
    have : ∑ d in n.divisors, weights d = weights 1 := by
      rw [hn, divisors_one, sum_singleton]
    rw [this, hw, one_pow]
  · rw [if_neg hn]
    apply sq_nonneg

set_option quotPrecheck false
variable (s : Sieve)

local notation "ν" => s.nu
local notation "P" => s.prodPrimes
local notation "a" => s.weights
local notation "X" => s.totalMass
local notation "R" => s.rem
local notation "g" => s.selbergTerms

theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquaredOfWeights w) =
      ∑ d1 in divisors P, ∑ d2 in divisors P,
        ν d1 / d1 * w d1 * (ν d2 / d2) * w d2 * (d1.gcd d2 / ν (d1.gcd d2)) :=
  by
  dsimp only [mainSum, lambdaSquaredOfWeights]
  trans (∑ d in divisors P, ∑ d1 in divisors d, ∑ d2 in divisors d, 
          if d = d1.lcm d2 then w d1 * w d2 * (ν d / ↑d) else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
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
  trans (∑ d1 in divisors P, ∑ d2 in divisors P, (∑ l in divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 / ↑d1 * w d1) * (ν d2 / ↑d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [s.nu_eq_conv_one_div_selbergTerms _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [←ite_mul_zero_right]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l in divisors P, ∑ d1 in divisors P, ∑ d2 in divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 / ↑d1 * w d1) * (ν d2 / ↑d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _; rw[sum_comm]; 
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [←ite_and_mul_zero, ←ite_mul_zero_right]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end Sieve

