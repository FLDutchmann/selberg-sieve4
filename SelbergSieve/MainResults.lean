/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module main_results
-/
import Mathlib.NumberTheory.ArithmeticFunction
import SelbergSieve.Selberg
import SelbergSieve.Sieve

open scoped BigOperators Nat.ArithmeticFunction

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

theorem fundamental_theorem_simple (s : Sieve) (y : ℝ) (hy : 1 ≤ y) :
    s.siftedSum ≤
      s.X / s.selbergBoundingSumAtLevel y +
        ∑ d in s.P.divisors, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |s.R d| else 0 :=
  s.selberg_bound_simple y hy

