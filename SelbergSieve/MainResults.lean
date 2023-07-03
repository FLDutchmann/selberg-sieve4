/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module main_results
-/
import Mathlib.NumberTheory.ArithmeticFunction
import SelbergSieve.Selberg
import SelbergSieve.SieveLemmas
import Mathlib.NumberTheory.PrimeCounting

open scoped BigOperators Nat.ArithmeticFunction Sieve Nat

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

theorem fundamental_theorem_simple (s : SelbergSieve) :
    s.siftedSum ≤
      s.totalMass / s.selbergBoundingSum +
        ∑ d in s.prodPrimes.divisors, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |s.rem d| else 0 :=
  s.selberg_bound_simple

#check Real.log

theorem primeCounting_ll : ∃ C, ∀ N, (π N:ℝ) ≤ C * N / Real.log N := by
  sorry
