/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import SelbergSieve.UpperBoundSieve 
import SelbergSieve.AuxResults

open scoped BigOperators 

open Finset Nat Real Aux

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

namespace Sieve

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
    rw [conv_lambda_sq_larger_sum _ n]
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