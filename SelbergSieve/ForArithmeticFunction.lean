/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Real.Basic
import SelbergSieve.Tactic.Multiplicativity

namespace Nat.ArithmeticFunction
open scoped Nat.ArithmeticFunction BigOperators Classical

theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 := by
  rw [moebius_apply_of_squarefree hl, ←pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 := by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]

theorem moebius_sq {n : ℕ} :
    μ n ^ 2 = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [Nat.isUnit_iff, zero_lt_two, pow_eq_zero_iff, moebius_eq_zero_of_not_squarefree h]



end Nat.ArithmeticFunction
