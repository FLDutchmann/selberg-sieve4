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
  
/- NOT YET PR'D -/
variable {R : Type _}

def prodDistinctFactors [CommMonoidWithZero R] (f : ℕ → R) : ArithmeticFunction R := 
  ⟨fun d => if d = 0 then 0 else ∏ p in d.factors.toFinset, f p, if_pos rfl⟩

open Std.ExtendedBinder

scoped syntax (name := bigproddvd) "∏ᵖ " extBinder " ∣ " term ", " term:67 : term
scoped macro_rules (kind := bigproddvd)
  | `(∏ᵖ $x:ident ∣ $n, $r) => `(prodDistinctFactors (fun $x ↦ $r) $n) 

scoped syntax (name := bigproddvdarith) "∏ᵖ " term:67 : term
scoped macro_rules (kind := bigproddvdarith)
  | `(∏ᵖ $f) => `(prodDistinctFactors $f) 

@[simp]
theorem prodDistinctFactors_apply [CommMonoidWithZero R] {f: ℕ → R} {n : ℕ} [hn : NeZero n] :
    ∏ᵖ p ∣ n, f p = ∏ p in n.factors.toFinset, f p := 
  if_neg (hn.ne)

theorem prodDistinctFactors_apply_of_ne_zero [CommMonoidWithZero R] {f: ℕ → R} {n : ℕ} (hn : n ≠ 0) :
    ∏ᵖ p ∣ n, f p = ∏ p in n.factors.toFinset, f p := 
  haveI : NeZero n := ⟨hn⟩
  prodDistinctFactors_apply

def rad : ArithmeticFunction ℕ := ∏ᵖ id

@[simp]
theorem rad_apply {n:ℕ} [hn : NeZero n] : 
    rad n = ∏ p in n.factors.toFinset, p := by
  unfold rad; simp

theorem rad_apply_of_ne_zero {n : ℕ} (hn : n ≠ 0) : 
    rad n = ∏ p in n.factors.toFinset, p := 
  haveI : NeZero n := ⟨hn⟩
  rad_apply

theorem rad_apply_of_squarefree {n : ℕ} (hn : Squarefree n) :
    rad n = n := by
  haveI : NeZero n := ⟨hn.ne_zero⟩
  rw [rad_apply]
  sorry

theorem prod_subset_factors_of_mult {R : Type _} [CommSemiring R] (f : Nat.ArithmeticFunction R) 
  (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) (l : ℕ) 
  (t : Finset ℕ) (ht : t ⊆ l.factors.toFinset) :
    ∏ a : ℕ in t, f a = f (∏ a in t, a) := by 
  apply (h_mult.map_prod ..).symm
  exact fun x hx y hy hxy => (Nat.coprime_primes (Nat.prime_of_mem_factors (List.mem_toFinset.mp (ht hx))) 
    (Nat.prime_of_mem_factors (List.mem_toFinset.mp (ht hy)))).mpr hxy

theorem eq_prod_set_factors_of_squarefree {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, p = l :=
  by
  erw [←l.factors.toFinset.prod_val]
  suffices l.factors.toFinset.val = l.factors by
    rw [this, Multiset.coe_prod]; exact l.prod_factors hl.ne_zero
  ext p
  rw [List.toFinset_val, Multiset.coe_count, Multiset.coe_count, List.count_dedup, eq_comm]
  exact List.count_eq_of_nodup ((squarefree_iff_nodup_factors (hl.ne_zero)).mp hl)

theorem prod_factors_sdiff {n : ℕ} (hn : Squarefree n) {t : Finset ℕ} (ht : t ⊆ n.factors.toFinset) :
    ∏ a in (n.factors.toFinset \ t), a = n / ∏ a in t, a := by
  apply symm
  suffices h : n = (∏ a in t, a) * ∏ a in (n.factors.toFinset \ t), a
  · conv => {lhs; rw [h]}
    exact Nat.mul_div_cancel_left _ $ Finset.prod_pos fun p hp => 
      (prime_of_mem_factors (List.mem_toFinset.mp (ht hp))).pos
  rw [←Finset.prod_union Finset.disjoint_sdiff]
  simp_rw [Finset.union_sdiff_of_subset ht, eq_prod_set_factors_of_squarefree hn]
  

set_option profiler true  
 
theorem prodDistinctFactors_mult [CommMonoidWithZero R] (f : ℕ → R) : IsMultiplicative (∏ᵖ f) :=
  by
  rw [Nat.ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · apply prodDistinctFactors_apply
  intro x y hx hy hxy
  haveI : NeZero x := ⟨hx⟩
  haveI : NeZero y := ⟨hy⟩ 
  simp_rw [prodDistinctFactors_apply]
  have h_disj := List.disjoint_toFinset_iff_disjoint.mpr (coprime_factors_disjoint hxy)
  rw[Nat.factors_mul_toFinset hx hy, ←Finset.prod_disjUnion h_disj, Finset.disjUnion_eq_union]

--Nat.sum_divisors_filter_squarefree
-- dependent on 5798
theorem prod_add_mult' {R : Type _} [CommSemiring R] (f g : ArithmeticFunction R) (hf : IsMultiplicative f) (hg : IsMultiplicative g)
  (n : ℕ) (hn : Squarefree n) :
    ∏ᵖ p ∣ n, (f + g) p = (f * g) n := by
  rw [prodDistinctFactors_apply_of_ne_zero hn.ne_zero]; simp_rw [add_apply (f:=f) (g:=g)]
  rw [Finset.prod_add, mul_apply, Nat.sum_divisorsAntidiagonal (f:= λ x y => f x * g y),  
    ←divisors_filter_squarefree_of_squarefree hn, Nat.sum_divisors_filter_squarefree $ Squarefree.ne_zero hn, 
    Nat.factors_eq]
  apply Finset.sum_congr rfl
  intro t ht
  erw [t.prod_val]
  unfold _root_.id
  erw [←prod_factors_sdiff hn (Finset.mem_powerset.mp ht),
    prod_subset_factors_of_mult _ hf n t (Finset.mem_powerset.mp ht),
    ←prod_subset_factors_of_mult _ hg n (_ \ t) (Finset.sdiff_subset _ t) ]
  /- This should be rfl   mathlib#5798 is merged -/
  try
  · apply congr_arg (_ * ·) $ Finset.prod_congr _ (fun _ _=> rfl)
    ext a
    simp_rw [Finset.mem_sdiff, @Finset.mem_sdiff _ fun a b => Classical.propDecidable (a = b)] 

theorem prod_add_mult {R : Type _} [CommSemiring R] (f : Nat.ArithmeticFunction R) (h_mult : f.IsMultiplicative) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, (1 + f p) = ∑ d in l.divisors, f d := by
  /-trans (prodDistinctFactors ((ζ:ArithmeticFunction R) + f) l)
  · rw [prodDistinctFactors_apply hl.ne_zero]
    apply Finset.prod_congr rfl; intro p hp
    rw [add_apply, natCoe_apply, zeta_apply_ne (Nat.prime_of_mem_factors $ List.mem_toFinset.mp hp).ne_zero, cast_one]
  rw [prod_add_mult' (ζ:ArithmeticFunction R) f isMultiplicative_zeta.nat_cast h_mult _ hl]
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (f:= fun x y => (ζ:ArithmeticFunction R) x * f y)]
  apply Finset.sum_congr rfl; intro d hd
  rw [natCoe_apply, zeta_apply_ne, cast_one, one_mul] -/
  
  conv => {lhs; congr; {skip}; ext p; rw [add_comm]}
  rw [Finset.prod_add]
  simp_rw [Finset.prod_eq_one fun _ _ => rfl, mul_one]
  rw [←l.divisors_filter_squarefree_of_squarefree hl, Nat.sum_divisors_filter_squarefree hl.ne_zero, 
    Nat.factors_eq]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_val]
  exact prod_subset_factors_of_mult f h_mult l t (Finset.mem_powerset.mp ht)

theorem prod_eq_moebius_sum {R : Type _} [CommRing R] (f : Nat.ArithmeticFunction R) (hf : f.IsMultiplicative) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, (1 - f p) = ∑ d in l.divisors, μ d * f d := by
  trans (∏ p in l.factors.toFinset, (1 + (pmul (μ:ArithmeticFunction R) f) p))
  · apply Finset.prod_congr rfl; intro p hp
    rw [pmul_apply, intCoe_apply, Nat.ArithmeticFunction.moebius_apply_prime 
        (Nat.prime_of_mem_factors (List.mem_toFinset.mp hp))]
    ring
  · rw [prod_add_mult (f:= pmul (μ : ArithmeticFunction R) f) 
    (isMultiplicative_moebius.int_cast.pmul hf) hl]
    simp_rw [pmul_apply, intCoe_apply]

#eval  ((zeta)^(7:ℕ)) 4

end Nat.ArithmeticFunction