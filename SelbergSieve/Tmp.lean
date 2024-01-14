/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.ArithmeticFunction

open Nat Nat.ArithmeticFunction BigOperators Finset

namespace Nat

open Finset

variable {ι : Type _} [DecidableEq ι] [DecidableEq (ι → ℕ)]

def piMulAntidiagonal (s : Finset ι) (n : ℕ) : Finset (ι → ℕ) :=
    (s.pi fun _ : ι => n.divisors)
    |>.map ⟨fun f i => if h : i ∈ s then f i h else 1,
      fun f g h => by ext i hi; simpa only [dif_pos hi] using congr_fun h i⟩
    |>.filter fun f => ∏ i in s, f i = n

@[simp]
theorem mem_piMulAntidiagonal {s : Finset ι} {d : ℕ} {f : ι → ℕ} :
    f ∈ piMulAntidiagonal s d ↔ ∏ i in s, f i = d ∧ (∀ i, i ∉ s → f i = 1) ∧ d ≠ 0 := by
  rw [piMulAntidiagonal, mem_filter, and_comm, and_congr_right]
  rintro rfl
  simp only [mem_map, mem_pi, mem_divisors, Nat.isUnit_iff, ne_eq, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨g, hgs, rfl⟩
    constructor
    · intro i hi
      simp_rw [dif_neg hi]
    · by_cases hs : s.Nonempty
      · obtain ⟨i, hi⟩ := hs.bex
        exact hgs i hi |>.2
      · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  · intro ⟨h, hd⟩
    use fun i _ => f i
    constructor
    · exact fun i hi => ⟨dvd_prod_of_mem f hi, hd⟩
    ext i
    split_ifs with hi
    · rfl
    · rw [h i hi]

@[simp]
theorem piMulAntidiagonal_zero {s : Finset ι} :
    piMulAntidiagonal s 0 = ∅ := by
  ext; simp

theorem piMulAntidiagonal_empty_of_ne_one (hn : n ≠ 1) :
    piMulAntidiagonal (∅ : Finset ι) n = ∅ := by
  ext; simp [hn.symm]

theorem dvd_of_mem_piMulAntidiagonal {s : Finset ι} {n : ℕ} {f : ι → ℕ} (hf : f ∈ piMulAntidiagonal s n) (i : ι):
    f i ∣ n := by
  rw [mem_piMulAntidiagonal] at hf
  rw [←hf.1]
  by_cases hs : i ∈ s
  · exact dvd_prod_of_mem f hs
  · rw [hf.2.1 i hs]; exact one_dvd (∏ i in s, f i)

theorem ne_zero_of_mem_piMulAntidiagonal {s : Finset ι} {n : ℕ} {f : ι → ℕ} (hf : f ∈ piMulAntidiagonal s n) (i : ι):
    f i ≠ 0 :=
  ne_zero_of_dvd_ne_zero (mem_piMulAntidiagonal.mp hf).2.2 (dvd_of_mem_piMulAntidiagonal hf i)

theorem prod_eq_of_mem_piMulAntidiagonal {s : Finset ι} {n : ℕ} {f : ι → ℕ} (hf : f ∈ piMulAntidiagonal s n):
    ∏ i in s, f i = n :=
  (mem_piMulAntidiagonal.mp hf).1

lemma filter_primeFactors {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    n.primeFactors.filter fun p => p ∣ m = m.primeFactors := by
  ext p
  simp only [mem_filter, mem_primeFactors, ne_eq, hn, not_false_eq_true, and_true,
    ne_zero_of_dvd_ne_zero hn hmn, and_congr_left_iff, and_iff_left_iff_imp]
  exact fun h _ ↦ h.trans hmn

lemma piMulAntidiagonal_exists_unique_prime_dvd {s : Finset ι} {n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.factors) (f : ι → ℕ) (hf : f ∈ piMulAntidiagonal s n) :
    ∃! i, i ∈ s ∧ p ∣ f i := by
  rw [mem_piMulAntidiagonal] at hf
  rw [mem_factors hf.2.2, ← hf.1, hp.1.prime.dvd_finset_prod_iff] at hp
  obtain ⟨i, his, hi⟩ := hp.2
  use i
  refine ⟨⟨his, hi⟩, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj.2⟩
  apply Nat.coprime_of_squarefree_mul
  apply hn.squarefree_of_dvd
  rw [←hf.1, ←Finset.mul_prod_erase _ _ (his),
    ←Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij, hj.1⟩), ←mul_assoc]
  apply Nat.dvd_mul_right

private def primeFactorsPiBij {s : Finset ι} (n : ℕ) : ∀ f ∈ (n.primeFactors.pi fun _ => s), ι → ℕ :=
  fun f _ i => ∏ p in Finset.filter (fun p => f p.1 p.2 = i) n.primeFactors.attach,  p

private theorem primeFactorsPiBij_img {s : Finset ι} (n : ℕ) (hn : Squarefree n)
  (f : (p : ℕ) → p ∈ n.primeFactors → ι) (hf : f ∈ pi n.primeFactors fun _ => s) :
    Nat.primeFactorsPiBij n f hf ∈ piMulAntidiagonal s n := by
  rw [mem_piMulAntidiagonal]
  rw [Finset.mem_pi] at hf
  refine ⟨?_, ?_, hn.ne_zero⟩
  · unfold Nat.primeFactorsPiBij
    rw [prod_fiberwise_of_maps_to, prod_attach (f := fun x => x)]
    apply prod_primeFactors_of_squarefree hn
    intro _ _
    apply hf
  · intro i hi
    apply prod_eq_one
    rintro ⟨p, hp⟩ h
    rw [mem_filter] at h
    rw [←h.2] at hi
    exfalso
    apply hi
    apply hf

private theorem primeFactorsPiBij_inj {s : Finset ι} (n : ℕ)
    (f g : (p : ℕ) → p ∈ n.primeFactors → ι) (hf : f ∈ pi n.primeFactors fun _ => s)
    (hg : g ∈ pi n.primeFactors fun _ => s) : Nat.primeFactorsPiBij n f hf = Nat.primeFactorsPiBij n g hg → f = g := by
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.primeFactorsPiBij]
  apply ne_of_mem_of_not_mem (s:= ({x | (p ∣ x)}:Set ℕ)) <;> simp_rw [Set.mem_setOf_eq]
  · rw [Finset.prod_filter]
    convert Finset.dvd_prod_of_mem _ (mem_attach (n.primeFactors) ⟨p, hp⟩)
    rw [if_pos rfl]
  · rw [mem_primeFactors] at hp
    rw [Prime.dvd_finset_prod_iff hp.1.prime]
    push_neg
    intro q hq
    rw [Nat.prime_dvd_prime_iff_eq hp.1 (Nat.prime_of_mem_factors $ List.mem_toFinset.mp q.2)]
    intro hpq; subst hpq
    rw [(mem_filter.mp hq).2] at hfg
    exact hfg rfl

private theorem primeFactorsPiBij_surj {s : Finset ι} (n : ℕ) (hn : Squarefree n)
    (t : ι → ℕ) (ht : t ∈ piMulAntidiagonal s n) : ∃ (g:_)
      (hg : g ∈ pi n.primeFactors fun _ => s), Nat.primeFactorsPiBij n g hg = t := by
  have exists_unique := fun (p : ℕ) (hp : p ∈ n.primeFactors) =>
    (piMulAntidiagonal_exists_unique_prime_dvd hn
      (mem_primeFactors_iff_mem_factors.mp hp) t ht)
  choose f hf hf_unique using exists_unique
  use f
  use ?_
  swap
  · simp only [mem_pi]
    intro p hp
    apply hf p hp |>.1
  funext i
  have : t i ∣ n := dvd_of_mem_piMulAntidiagonal ht _
  trans (∏ p in n.primeFactors.attach, if p.1 ∣ t i then p else 1)
  · rw [Nat.primeFactorsPiBij, ←prod_filter]
    congr
    ext ⟨p, hp⟩
    refine ⟨by rintro rfl; apply hf p hp |>.2, fun h => (hf_unique p hp i ⟨?_, h⟩).symm⟩
    by_contra hs
    rw [mem_piMulAntidiagonal] at ht
    simp only [ht.2.1 i hs ,Nat.isUnit_iff, Nat.dvd_one] at h
    simp only [h, List.mem_toFinset] at hp
    simpa[not_prime_one] using Nat.prime_of_mem_primeFactors hp
  rw [prod_attach (f:=fun p => if p ∣ t i then p else 1), ←Finset.prod_filter]
  rw [filter_primeFactors this hn.ne_zero]
  apply prod_primeFactors_of_squarefree $ hn.squarefree_of_dvd this

theorem card_piMulAntidiagonal_pi {s : Finset ι} (n : ℕ) (hn : Squarefree n) :
    (n.primeFactors.pi (fun _ => s)).card =
      (piMulAntidiagonal s n).card := by
  exact Finset.card_congr (Nat.primeFactorsPiBij n (s:=s)) (primeFactorsPiBij_img n hn)
    (primeFactorsPiBij_inj n) (primeFactorsPiBij_surj n hn)

theorem card_piMulAntidiagonal {s : Finset ι} {d : ℕ} (hd : Squarefree d) :
    (piMulAntidiagonal s d).card = s.card ^ ω d := by
  rw [←card_piMulAntidiagonal_pi d hd, Finset.card_pi, Finset.prod_const,
    cardDistinctFactors_apply, ←toFinset_factors, List.card_toFinset]

theorem card_piMulAntidiagonal_fin {d : ℕ} (hd : Squarefree d) (k : ℕ) :
    (piMulAntidiagonal (univ : Finset <| Fin k) d).card = k ^ ω d := by
  rw [card_piMulAntidiagonal hd, card_fin]
