/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import SelbergSieve.Selberg

open scoped Nat Nat.ArithmeticFunction
/--
  https://leanprover-community.github.io/mathlib_docs/analysis/inner_product_space/basic.html#real_inner_le_norm
  https://leanprover-community.github.io/mathlib_docs/analysis/inner_product_space/pi_L2.html#orthonormal_basis.sum_inner_mul_inner
  
-/

def primeSieve (N : ℕ) : SelbergSieve := {
  nu := ζ
  nu_mult := sorry
  nu_pos_of_prime := sorry
  nu_lt_self_of_prime := sorry
  support := Finset.Icc 1 N
  prodPrimes := sorry
  prodPrimes_squarefree := sorry
  weights := fun _ => 1
  ha_nonneg := sorry
  totalMass := N
  level := sorry
  one_le_level := sorry
}

def CompletelyMultiplicative (f : Nat.ArithmeticFunction ℝ) : Prop := sorry

lemma tmp (s : Sieve) (hnu : CompletelyMultiplicative s.nu) :  sorry := sorry