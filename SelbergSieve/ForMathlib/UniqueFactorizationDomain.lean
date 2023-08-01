/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.RingTheory.UniqueFactorizationDomain

open BigOperators

namespace UniqueFactorizationMonoid

variable {α : Type u_1} [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] [DecidableEq α]

noncomputable def radical (n : α) := ∏ p in (normalizedFactors n).toFinset, p