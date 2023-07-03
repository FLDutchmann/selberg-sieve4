/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Data.Nat.Squarefree

namespace Tmp

#check Nat.mul_dvd_mul

theorem coprime_of_mul_squarefree (x y : ℕ) (h : Squarefree $ x * y) : x.coprime y :=
  by
  by_contra h_ncop
  cases' Nat.Prime.not_coprime_iff_dvd.mp h_ncop with p hp
  exact (Nat.squarefree_iff_prime_squarefree.mp h) p hp.1 $ Nat.mul_dvd_mul hp.2.1 hp.2.2

theorem coprime_of_mul_squarefree' {M : Type _} [CancelCommMonoidWithZero M] [UniqueFactorizationMonoid M] 
  (x y : M) (h : Squarefree $ x*y) : 
    ∀ (p : M), p ∣ x → p ∣ y → IsUnit p := by
  by_contra h_ncop; push_neg at h_ncop
  cases' h_ncop with p hp
  exact hp.2.2 $ h p $ mul_dvd_mul hp.1 hp.2.1

#exit
-- Read : Unique Factorization Domain
theorem isCoprime_of_mul_squarefree {R : Type _} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [GCDMonoid R]
  (x y : R) (h : Squarefree $ x*y) : 
    IsCoprime x y := by
  apply?
  apply isCoprime_of_prime_dvd
  · sorry
  by_contra h; push_neg at h
  cases' h with p hp

  sorry