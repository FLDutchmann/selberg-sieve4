/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Real.Basic
import SelbergSieve.Multiplicativity
namespace Nat.ArithmeticFunction
open scoped Nat.ArithmeticFunction BigOperators Classical


open UniqueFactorizationMonoid

-- theorem test [AddCommMonoid R] (n : ℕ) (hn : Squarefree n) (f : ℕ → ℕ → R):
--   ∑ x in n.divisorsAntidiagonal, f x.fst x.snd =
--     ∑ t in (normalizedFactors n).powerset.toFinset, f (t.prod) (((normalizedFactors n) - t).prod) := by


end Nat.ArithmeticFunction
