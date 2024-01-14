/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

namespace Aux

open BigOperators Nat.ArithmeticFunction
/- Lemmas in this file are singled out as suitible for addition to Mathlib4 with minor modifications -/


-- theorem prime_dvd_lcm_iff (a b p : ℕ) (hp : p.Prime) : p ∣ x.lcm y ↔ p ∣ x ∨ p ∣ y :=
--   ⟨ fun h => (Nat.Prime.dvd_mul hp).mp (Nat.dvd_trans h (Nat.lcm_dvd_mul x y)),
--     fun h => Or.elim h (fun hx => Trans.trans hx (Nat.dvd_lcm_left x y))
--       (fun hy => Trans.trans hy (Nat.dvd_lcm_right x y)) ⟩


example (a b : ℕ) : a ≤ b ∨ b ≤ a := by exact Nat.le_or_le a b

variable {R : Type*}

theorem mult_lcm_eq_of_ne_zero [CommGroupWithZero R] (f : Nat.ArithmeticFunction R) (h_mult : f.IsMultiplicative) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [←h_mult.lcm_apply_mul_gcd_apply]
  field_simp

theorem prod_factors_of_mult (f : Nat.ArithmeticFunction ℝ) (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a : ℕ in l.primeFactors, f a = f l := by
  rw [←IsMultiplicative.map_prod_of_subset_primeFactors h_mult l _ Finset.Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hl]

end Aux
