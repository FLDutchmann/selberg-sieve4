/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Real.Basic

namespace Nat.ArithmeticFunction
open scoped Nat.ArithmeticFunction BigOperators Classical

theorem prod_factors_sdiff_of_squarefree {n : ℕ} (hn : Squarefree n) {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) :
    ∏ a in (n.primeFactors \ t), a = n / ∏ a in t, a := by
  refine symm $ Nat.div_eq_of_eq_mul_left (Finset.prod_pos
    fun p hp => (prime_of_mem_factors (List.mem_toFinset.mp (ht hp))).pos) ?_
  rw [Finset.prod_sdiff ht, prod_primeFactors_of_squarefree hn]

variable {R : Type _}

def prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) : ArithmeticFunction R :=
  ⟨fun d => if d = 0 then 0 else ∏ p in d.primeFactors, f p, if_pos rfl⟩

open Std.ExtendedBinder

scoped syntax (name := bigproddvd) "∏ᵖ " extBinder " ∣ " term ", " term:67 : term
scoped macro_rules (kind := bigproddvd)
  | `(∏ᵖ $x:ident ∣ $n, $r) => `(prodPrimeFactors (fun $x ↦ $r) $n)

scoped syntax (name := bigproddvdarith) "∏ᵖ " term:67 : term
scoped macro_rules (kind := bigproddvdarith)
  | `(∏ᵖ $f) => `(prodPrimeFactors $f)

@[simp]
theorem prodPrimeFactors_apply [CommMonoidWithZero R] {f: ℕ → R} {n : ℕ} [hn : NeZero n] :
    ∏ᵖ p ∣ n, f p = ∏ p in n.primeFactors, f p :=
  if_neg (hn.ne)

theorem prodPrimeFactors_apply_of_ne_zero [CommMonoidWithZero R] {f: ℕ → R} {n : ℕ} (hn : n ≠ 0) :
    ∏ᵖ p ∣ n, f p = ∏ p in n.primeFactors, f p :=
  haveI : NeZero n := ⟨hn⟩
  prodPrimeFactors_apply

theorem IsMultiplicative.map_prod_of_prime {R : Type _} [CommSemiring R] {f : Nat.ArithmeticFunction R}
    (h_mult : Nat.ArithmeticFunction.IsMultiplicative f)
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    f (∏ a in t, a) = ∏ a : ℕ in t, f a :=
  map_prod _ h_mult t fun x hx y hy hxy => (coprime_primes (ht x hx) (ht y hy)).mpr hxy

theorem IsMultiplicative.map_prod_of_subset_factors {R : Type _} [CommSemiring R] {f : Nat.ArithmeticFunction R}
    (h_mult : Nat.ArithmeticFunction.IsMultiplicative f) (l : ℕ)
    (t : Finset ℕ) (ht : t ⊆ l.primeFactors) :
     f (∏ a in t, a) = ∏ a : ℕ in t, f a :=
  map_prod_of_prime h_mult t fun _ a => prime_of_mem_primeFactors (ht a)

theorem IsMultiplicative.prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) : IsMultiplicative (∏ᵖ f) :=
  by
  rw [Nat.ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · apply prodPrimeFactors_apply
  intro x y hx hy hxy
  haveI : NeZero x := ⟨hx⟩
  haveI : NeZero y := ⟨hy⟩
  simp_rw [prodPrimeFactors_apply]
  rw[Nat.primeFactors_mul hx hy, ←Finset.prod_union hxy.disjoint_primeFactors]

theorem IsMultiplicative.prodPrimeFactors_add_of_squarefree {R : Type _} [CommSemiring R] {f g : ArithmeticFunction R} (hf : IsMultiplicative f) (hg : IsMultiplicative g)
  (n : ℕ) (hn : Squarefree n) :
    ∏ᵖ p ∣ n, (f + g) p = (f * g) n := by
  rw [prodPrimeFactors_apply_of_ne_zero hn.ne_zero]; simp_rw [add_apply (f:=f) (g:=g)]
  rw [Finset.prod_add, mul_apply, Nat.sum_divisorsAntidiagonal (f:= λ x y => f x * g y),
    ←divisors_filter_squarefree_of_squarefree hn, Nat.sum_divisors_filter_squarefree hn.ne_zero,
    Nat.factors_eq]
  apply Finset.sum_congr rfl
  intro t ht
  erw [t.prod_val, ←prod_factors_sdiff_of_squarefree hn (Finset.mem_powerset.mp ht),
    hf.map_prod_of_subset_factors n t (Finset.mem_powerset.mp ht),
    ←hg.map_prod_of_subset_factors n (_ \ t) (Finset.sdiff_subset _ t) ]

theorem IsMultiplicative.prodPrimeFactors_one_add_of_squarefree {R : Type _} [CommSemiring R] {f : Nat.ArithmeticFunction R}
  (h_mult : f.IsMultiplicative) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.primeFactors, (1 + f p) = ∑ d in l.divisors, f d := by
  haveI : NeZero l := ⟨hl.ne_zero⟩
  trans (∏ᵖ p ∣ l, ((ζ:ArithmeticFunction R) + f) p)
  · simp_rw [prodPrimeFactors_apply, add_apply, natCoe_apply]
    apply Finset.prod_congr rfl; intro p hp;
    rw [zeta_apply_ne (Nat.prime_of_mem_factors $ List.mem_toFinset.mp hp).ne_zero, cast_one]
  rw [isMultiplicative_zeta.nat_cast.prodPrimeFactors_add_of_squarefree h_mult _ hl,
    coe_zeta_mul_apply]

theorem IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree {R : Type _} [CommRing R] (f : Nat.ArithmeticFunction R) (hf : f.IsMultiplicative) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.primeFactors, (1 - f p) = ∑ d in l.divisors, μ d * f d := by
  trans (∏ p in l.primeFactors, (1 + ((μ:ArithmeticFunction R).pmul f) p))
  · apply Finset.prod_congr rfl; intro p hp
    rw [pmul_apply, intCoe_apply, Nat.ArithmeticFunction.moebius_apply_prime
        (Nat.prime_of_mem_factors (List.mem_toFinset.mp hp))]
    ring
  · rw [(isMultiplicative_moebius.int_cast.pmul hf).prodPrimeFactors_one_add_of_squarefree hl]
    simp_rw [pmul_apply, intCoe_apply]

open UniqueFactorizationMonoid

-- theorem test [AddCommMonoid R] (n : ℕ) (hn : Squarefree n) (f : ℕ → ℕ → R):
--   ∑ x in n.divisorsAntidiagonal, f x.fst x.snd =
--     ∑ t in (normalizedFactors n).powerset.toFinset, f (t.prod) (((normalizedFactors n) - t).prod) := by


end Nat.ArithmeticFunction
