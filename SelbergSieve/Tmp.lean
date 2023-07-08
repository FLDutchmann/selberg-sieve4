/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Algebra.Squarefree

namespace Tmp

theorem coprime_of_squarefree_mul' {M : Type _} [CommMonoid M]
  (x y : M) (h : Squarefree $ x*y) : 
    ∀ (p : M), p ∣ x → p ∣ y → IsUnit p :=
  fun p hx hy => h p $ mul_dvd_mul hx hy
#exit