/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.NumberTheory.ArithmeticFunction


open Nat.ArithmeticFunction Classical
open scoped BigOperators Classical

theorem divisors_filter_squarefree_of_squarefree (n : ℕ) (hn : Squarefree n) :
    n.divisors.filter Squarefree = n.divisors := sorry

theorem prod_subset_factors_of_mult {R : Type _} [CommSemiring R] (f : Nat.ArithmeticFunction R) 
  (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) (l : ℕ) 
  (t : Finset ℕ) (ht : t ⊆ l.factors.toFinset) :
    ∏ a : ℕ in t, f a = f (∏ a in t, a) := sorry

theorem prod_compl_factors [DecidableEq ℕ] {n : ℕ} (hn : Squarefree n) {t : Finset ℕ} (ht : t ⊆ n.factors.toFinset) :
    ∏ a in (n.factors.toFinset \ t), a = n / (∏ a in t, a) := by
  sorry

--Nat.sum_divisors_filter_squarefree
/-  -/
theorem prod_add_mult' {R : Type _} [CommSemiring R] (f g : Nat.ArithmeticFunction R) (hf : IsMultiplicative f) (hg : IsMultiplicative g)
  (n : ℕ) (hn : Squarefree n) :
    ∏ p in n.factors.toFinset, (f p + g p) = (f * g) n := by
  rw [Finset.prod_add, mul_apply, Nat.sum_divisorsAntidiagonal (f:= λ x y => f x * g y),  
    ←divisors_filter_squarefree_of_squarefree _ hn, Nat.sum_divisors_filter_squarefree $ Squarefree.ne_zero hn, 
    Nat.factors_eq]
  apply Finset.sum_congr rfl
  intro t ht
  erw [Finset.prod_val]
  unfold _root_.id
  erw [←prod_compl_factors hn (Finset.mem_powerset.mp ht),
    prod_subset_factors_of_mult _ hf n t (Finset.mem_powerset.mp ht),
    ←prod_subset_factors_of_mult _ hg n (_ \ t) (Finset.sdiff_subset _ t) ]
  /- This should be rfl   mathlib#5798 is merged -/
  apply congr_arg (_ * ·)
  apply Finset.prod_congr _ (fun _ _=> rfl)
  ext a
  simp_rw [Finset.mem_sdiff, @Finset.mem_sdiff _ fun a b => propDecidable (a = b)] 
