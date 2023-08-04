/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.NumberTheory.ArithmeticFunction

open BigOperators

namespace UniqueFactorizationMonoid

variable {α : Type u_1} [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] [DecidableEq α]

noncomputable def radical (n : α) := if n = 0 then 0 else ∏ p in (normalizedFactors n).toFinset, p

theorem radical_zero :
    radical 0 = 0 := by
  unfold radical
  rw [if_pos rfl]
  
theorem radical_apply {n : α} [hn : NeZero n] :
    radical n = ∏ p in (normalizedFactors n).toFinset, p := by
  unfold radical
  rw [if_neg hn.ne]

theorem radical_associated_of_squarefree {n : α} (hn : Squarefree n) :
    Associated (radical n) n := by 
  refine dvd_dvd_iff_associated.mp ?_
  sorry

theorem prime_dvd_radical_iff (n p: α) (hp : Prime p) : 
    p ∣ radical n ↔ p ∣ n := by
  sorry

end UniqueFactorizationMonoid

open UniqueFactorizationMonoid
namespace Nat

theorem radical_apply {n : ℕ} [hn : NeZero n] :
    radical n = ∏ p in n.factors.toFinset, p := by
  rw [UniqueFactorizationMonoid.radical_apply, factors_eq]
  rfl

theorem radical_apply_of_squarefree {n : ℕ} (hn : Squarefree n) :
    radical n = n := by
  sorry
end Nat

#check radical 3