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

theorem piMulAntidiagonal_one {s : Finset ι} :
    piMulAntidiagonal s 1 = {fun _ => 1} := by
  ext f; simp only [mem_piMulAntidiagonal, and_true, mem_singleton]
  constructor
  · intro ⟨hf, h, _⟩; ext i;
    rw [←Nat.dvd_one, ←hf];
    by_cases hi : i ∈ s
    · exact dvd_prod_of_mem f hi
    rw [h i hi]; exact one_dvd (∏ i in s, f i)
  · rintro rfl; simp only [prod_const_one, implies_true, ne_eq, one_ne_zero, not_false_eq_true,
    and_self]

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

theorem piMulAntidiagonal_univ_eq [Fintype ι] (d P: ℕ) (hdP : d ∣ P) (hP : P ≠ 0):
    piMulAntidiagonal univ d =
      (Fintype.piFinset fun _ : ι => P.divisors).filter fun f => ∏ i, f i = d := by
  ext f
  simp only [mem_univ, not_true, IsEmpty.forall_iff, implies_true, ne_eq, true_and,
    Fintype.mem_piFinset, mem_divisors, Nat.isUnit_iff, mem_filter]
  constructor
  · intro hf
    refine ⟨?_, prod_eq_of_mem_piMulAntidiagonal hf⟩
    exact fun i => ⟨(dvd_of_mem_piMulAntidiagonal hf i).trans hdP, hP⟩
  · rw [mem_piMulAntidiagonal]
    exact fun ⟨_, hprod⟩ => ⟨hprod, by simp, ne_zero_of_dvd_ne_zero hP hdP⟩

lemma image_apply_piMulAntidiagonal {s : Finset ι} (hs : s.Nontrivial) {n : ℕ} {i : ι} (hi : i ∈ s) :
    (piMulAntidiagonal s n).image (fun f => f i) = divisors n := by
  ext k
  simp only [mem_image, ne_eq, mem_divisors, Nat.isUnit_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨dvd_of_mem_piMulAntidiagonal hf _, (mem_piMulAntidiagonal.mp hf).2.2⟩
  · simp_rw [mem_piMulAntidiagonal]
    rintro ⟨⟨r, rfl⟩, hn⟩
    obtain ⟨i', hi', hi_ne⟩ := hs.exists_ne i
    use fun j => if j = i then k else if j = i' then r else 1
    simp only [ite_true, and_true, hn]
    rw [←Finset.mul_prod_erase (a:=i) (h:=hi),
      ←Finset.mul_prod_erase (a:= i')]
    · rw [if_neg hi_ne, if_pos rfl, if_pos rfl, prod_eq_one]
      refine ⟨by ring, ?_, hn⟩
      intro j hj
      rw [if_neg, if_neg]
      · exact Ne.symm <| ne_of_mem_of_not_mem hi' hj
      · exact Ne.symm <| ne_of_mem_of_not_mem hi hj
      simp only [mem_erase, ne_eq, not_and, and_imp]
      intro j hji' hji
      simp only [hji, hji', ite_false, implies_true]
    exact mem_erase.mpr ⟨hi_ne, hi'⟩

lemma image_piFinTwoEquiv {n : ℕ} :
    (piMulAntidiagonal (univ : Finset <| Fin 2) n).image (piFinTwoEquiv $ fun _ => ℕ) = divisorsAntidiagonal n := by
  ext x
  simp only [piFinTwoEquiv_apply, mem_image, mem_piMulAntidiagonal, Fin.prod_univ_two, ne_eq,
    mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨y, ⟨h1, _, h2⟩, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h, hn⟩
    use fun i => if i = 0 then x.fst else x.snd
    simp (config:={decide:=true}) only [ite_true, ite_false, h, mem_univ, not_true, IsEmpty.forall_iff, forall_const, not_false_eq_true,
      and_self, Prod.mk.eta, hn]

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

private def bij (n : ℕ) : ((a : ℕ) → (a ∈ n.primeFactors) → ι) → (ι → ℕ) :=
  fun f i => ∏ p in Finset.filter (fun p => f p.1 p.2 = i) n.primeFactors.attach, p

private theorem img_bij {s : Finset ι} (n : ℕ) (hn : Squarefree n) :
    (n.primeFactors.pi fun _ => s).image (bij n) = piMulAntidiagonal s n := by
  ext f
  unfold Nat.bij
  constructor
  · simp only [mem_image, mem_pi, ne_eq, mem_piMulAntidiagonal]
    rintro ⟨f, hf, rfl⟩
    refine ⟨?_, ?_, hn.ne_zero⟩
    · rw [prod_fiberwise_of_maps_to, prod_attach (f := fun x => x)]
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
  · rintro hf
    simp only [filter_congr_decidable, mem_image, mem_pi, ne_eq]
    have exists_unique := fun (p : ℕ) (hp : p ∈ n.primeFactors) =>
      (piMulAntidiagonal_exists_unique_prime_dvd hn
        (mem_primeFactors_iff_mem_factors.mp hp) f hf)
    choose g hg hg_unique using exists_unique
    refine ⟨g, fun p hp => hg p hp |>.1, ?_⟩
    funext i
    have : f i ∣ n := dvd_of_mem_piMulAntidiagonal hf _
    trans (∏ p in n.primeFactors.attach, if p.1 ∣ f i then p else 1)
    · rw [←prod_filter]
      congr
      ext ⟨p, hp⟩
      refine ⟨by rintro rfl; apply hg p hp |>.2, fun h => (hg_unique p hp i ⟨?_, h⟩).symm⟩
      by_contra hs
      rw [mem_piMulAntidiagonal] at hf
      simp only [hf.2.1 i hs ,Nat.isUnit_iff, Nat.dvd_one] at h
      simp only [h] at hp
      simpa[not_prime_one] using Nat.prime_of_mem_primeFactors hp
    rw [prod_attach (f:=fun p => if p ∣ f i then p else 1), ←Finset.prod_filter]
    rw [filter_primeFactors this hn.ne_zero]
    apply prod_factors_toFinset_of_squarefree $ hn.squarefree_of_dvd this


private theorem bij_injOn {s : Finset ι} (n : ℕ) (hn : Squarefree n) :
    Set.InjOn (bij (ι:=ι) n) ↑(n.primeFactors.pi fun _ => s) := by
  intro f _ g _
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.bij]
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
  apply prod_factors_toFinset_of_squarefree $ hn.squarefree_of_dvd this

theorem card_piMulAntidiagonal_pi {s : Finset ι} (n : ℕ) (hn : Squarefree n) :
    (n.factors.toFinset.pi (fun _ => s)).card =
      (piMulAntidiagonal s n).card := by
  rw[←img_bij _ hn]
  exact Finset.card_image_of_injOn (bij_injOn _ hn) |>.symm

theorem card_piMulAntidiagonal {s : Finset ι} {d : ℕ} (hd : Squarefree d) :
    (piMulAntidiagonal s d).card = s.card ^ ω d := by
  rw [←card_piMulAntidiagonal_pi d hd, Finset.card_pi, Finset.prod_const,
    cardDistinctFactors_apply, List.card_toFinset]

theorem card_piMulAntidiagonal_fin {d : ℕ} (hd : Squarefree d) (k : ℕ) :
    (piMulAntidiagonal (univ : Finset <| Fin k) d).card = k ^ ω d := by
  rw [card_piMulAntidiagonal hd, card_fin]

@[reducible]
private def f : ∀ (a : Fin 3 → ℕ) (_ : a ∈ piMulAntidiagonal univ n), ℕ × ℕ := fun a _ =>
    (a 0 * a 1, a 0 * a 2)

private theorem piMulAntidiagonal_three : ∀ (a : Fin 3 → ℕ) (_ : a ∈ piMulAntidiagonal univ n), a 0 * a 1 * a 2 = n := by
    intro a ha
    rw [← (mem_piMulAntidiagonal.mp ha).1, Fin.prod_univ_three a]

private theorem f_img {n : ℕ} (hn : Squarefree n) : ∀ (a : Fin 3 → ℕ) (ha : a ∈ piMulAntidiagonal univ n),
      f a ha ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) := by
  intro a ha
  rw [mem_filter, Finset.mem_product, mem_divisors, mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ←piMulAntidiagonal_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left, Nat.Coprime.lcm_eq_mul]
  · ring
  refine coprime_of_squarefree_mul (hn.squarefree_of_dvd ?_)
  use a 0; rw [←piMulAntidiagonal_three a ha]; ring

private theorem f_inj {n : ℕ} :
    ∀ (a b : Fin 3 → ℕ) (ha : a ∈ piMulAntidiagonal univ n) (hb : b ∈ piMulAntidiagonal univ n),
      f a ha = f b hb → a = b := by
  intro a b ha hb hfab
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2
  · rw [piMulAntidiagonal_three a ha, hfab1, piMulAntidiagonal_three b hb]
  have hab2 : a 2 = b 2
  · rw [← mul_right_inj' $ mul_ne_zero (ne_zero_of_mem_piMulAntidiagonal ha 0)
      (ne_zero_of_mem_piMulAntidiagonal ha 1)]
    exact hprods
  have hab0 : a 0 = b 0
  · rw [hab2] at hfab2
    exact (mul_left_inj' $ ne_zero_of_mem_piMulAntidiagonal hb 2).mp hfab2;
  have hab1 : a 1 = b 1
  · rw [hab0] at hfab1
    exact (mul_right_inj' $ ne_zero_of_mem_piMulAntidiagonal hb 0).mp hfab1;
  funext i; fin_cases i <;> assumption

private theorem f_surj {n : ℕ} (hn : n ≠ 0) :
    ∀ b : ℕ × ℕ,
      b ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) →
        ∃ (a : Fin 3 → ℕ) (ha : a ∈ piMulAntidiagonal univ n), f a ha = b := by
  intro b hb
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := ![g, b.fst/g, b.snd/g]
  have ha : a ∈ piMulAntidiagonal univ n := by
    rw [mem_piMulAntidiagonal]
    rw [mem_filter, Finset.mem_product] at hb
    refine ⟨?_, ?_, hn⟩
    · rw [Fin.prod_univ_three a]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _), ←hb.2, lcm,
        Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
    · simp only [mem_univ, not_true, IsEmpty.forall_iff, forall_const]
  use a; use ha
  apply Prod.ext <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    <;> apply Nat.mul_div_cancel'
  · apply Nat.gcd_dvd_left
  · apply Nat.gcd_dvd_right

theorem card_lcm_eq {n : ℕ} (hn : Squarefree n) :
    Finset.card ((n.divisors ×ˢ n.divisors).filter fun ⟨x, y⟩ => x.lcm y = n) =
      3 ^ ω n := by
  rw [← card_piMulAntidiagonal_fin hn 3, eq_comm]
  apply Finset.card_congr f (f_img hn) (f_inj) (f_surj hn.ne_zero)

end Nat
