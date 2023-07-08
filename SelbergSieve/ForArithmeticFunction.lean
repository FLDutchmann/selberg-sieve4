/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.NumberTheory.ArithmeticFunction

namespace Nat.ArithmeticFunction
open scoped Nat.ArithmeticFunction

def pdiv {R : Type _} [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R := 
  ⟨fun n => f n / g n, by simp only [map_zero, ne_eq, not_true, div_zero]⟩

theorem pdiv_apply {R : Type _} [GroupWithZero R] (f g : ArithmeticFunction R) (n : ℕ): 
    pdiv f g n = f n / g n := rfl

theorem pdiv_zeta  {R : Type _} [DivisionSemiring R] (f : ArithmeticFunction R) :
    pdiv f (Nat.ArithmeticFunction.natToArithmeticFunction zeta) = f := by
  ext n
  by_cases hn : n = 0
  · rw [hn, map_zero, map_zero]  
  rw [pdiv_apply, natCoe_apply, zeta_apply_ne hn, cast_one, div_one]

theorem IsMultiplicative.pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f) (hg : IsMultiplicative g): 
    IsMultiplicative (pdiv f g) :=
  by
  constructor
  · rw [pdiv_apply, IsMultiplicative.map_one hf, IsMultiplicative.map_one hg, one_div_one]
  intro x y hxy
  simp_rw [pdiv_apply]
  rw [IsMultiplicative.map_mul_of_coprime hf hxy, IsMultiplicative.map_mul_of_coprime hg hxy, ←div_div,
    div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  exact mul_mul_mul_comm _ _ _ _
  

end Nat.ArithmeticFunction