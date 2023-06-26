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

end Sieve