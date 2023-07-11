/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Data.Nat.Squarefree

namespace Nat

theorem divisors_filter_squarefree_of_squarefree (n : ℕ) (hn : Squarefree n) :
    n.divisors.filter Squarefree = n.divisors := by
  ext d; constructor
  · apply Finset.filter_subset
  intro hd; rw[Finset.mem_filter]
  exact ⟨hd, Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hn⟩

end Nat