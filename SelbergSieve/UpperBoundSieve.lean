/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction

open scoped BigOperators ArithmeticFunction

namespace Sieve

def UpperMoebius (μ_plus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n=1 then 1 else 0) ≤ ∑ d in n.divisors, μ_plus d

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : UpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

def LowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d in n.divisors, μMinus d ≤ (if n=1 then 1 else 0)

structure LowerBoundSieve where mk ::
  μMinus : ℕ → ℝ
  hμMinus : LowerMoebius μMinus

instance lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus

end Sieve
