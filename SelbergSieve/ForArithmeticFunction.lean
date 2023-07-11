/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Real.Basic
import SelbergSieve.ForNatSquarefree


namespace Nat.ArithmeticFunction
open scoped Nat.ArithmeticFunction BigOperators Classical

def pdiv {R : Type _} [GroupWithZero R] (f g : ArithmeticFunction R) : ArithmeticFunction R := 
  ⟨fun n => f n / g n, by simp only [map_zero, ne_eq, not_true, div_zero]⟩

theorem pdiv_apply {R : Type _} [GroupWithZero R] (f g : ArithmeticFunction R) (n : ℕ) : 
    pdiv f g n = f n / g n := rfl

theorem pdiv_zeta  {R : Type _} [DivisionSemiring R] (f : ArithmeticFunction R) :
    pdiv f (Nat.ArithmeticFunction.natToArithmeticFunction zeta) = f := by
  ext n
  by_cases hn : n = 0
  · rw [hn, map_zero, map_zero]  
  rw [pdiv_apply, natCoe_apply, zeta_apply_ne hn, cast_one, div_one]

theorem IsMultiplicative.pdiv [CommGroupWithZero R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f) (hg : IsMultiplicative g): 
    IsMultiplicative (pdiv f g) :=
  by
  constructor
  · rw [pdiv_apply, IsMultiplicative.map_one hf, IsMultiplicative.map_one hg, one_div_one]
  intro x y hxy
  simp_rw [pdiv_apply]
  rw [IsMultiplicative.map_mul_of_coprime hf hxy, IsMultiplicative.map_mul_of_coprime hg hxy, ←div_div,
    div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  exact mul_mul_mul_comm _ _ _ _
  

theorem prod_subset_factors_of_mult {R : Type _} [CommSemiring R] (f : Nat.ArithmeticFunction R) 
  (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) (l : ℕ) 
  (t : Finset ℕ) (ht : t ⊆ l.factors.toFinset) :
    ∏ a : ℕ in t, f a = f (∏ a in t, a) := by 
  rw [Nat.ArithmeticFunction.IsMultiplicative.map_prod _ h_mult]
  intro x hx y hy hxy
  exact (Nat.coprime_primes (Nat.prime_of_mem_factors (List.mem_toFinset.mp (ht hx))) 
    (Nat.prime_of_mem_factors (List.mem_toFinset.mp (ht hy)))).mpr hxy

theorem prod_compl_factors {n : ℕ} (hn : Squarefree n) {t : Finset ℕ} (ht : t ⊆ n.factors.toFinset) :
    ∏ a in (n.factors.toFinset \ t), a = n / ∏ a in t, a := by
  sorry

--Nat.sum_divisors_filter_squarefree
-- dependent on 5798
theorem prod_add_mult' {R : Type _} [CommSemiring R] (f g : ArithmeticFunction R) (hf : IsMultiplicative f) (hg : IsMultiplicative g)
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
  simp_rw [Finset.mem_sdiff, @Finset.mem_sdiff _ fun a b => Classical.propDecidable (a = b)] 

end Nat.ArithmeticFunction