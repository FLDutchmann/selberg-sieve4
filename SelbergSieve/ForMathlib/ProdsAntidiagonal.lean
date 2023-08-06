/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.ArithmeticFunction

open Nat Nat.ArithmeticFunction BigOperators Finset


namespace CanonicallyOrderedMonoid

variable {α : Type u} {ι : Type v} [DecidableEq α] [DecidableEq ι] [CanonicallyOrderedMonoid α] 
  [DecidablePred fun n : α => Set.Finite (Set.Iic n)] 

@[to_additive]
noncomputable def antidiagonalProd (s : Finset ι) (n : α)  : Finset (ι → α) :=
  if 
    h : Set.Finite (Set.Iic n) 
  then 
    haveI : Fintype (Set.Iic n) := Set.Finite.fintype h
    Finset.filter (fun f => (∏ d in s, f d) = n)
      ((s.pi (fun _ => Set.toFinset (Set.Iic n))).map 
        (⟨fun f i => if h : i ∈ s then f i h else 1, 
          fun f g h => by ext i hi; simpa [dif_pos hi] using congr_fun h i⟩))
  else 
    if s = ∅ then {fun _ => 1} else ∅

theorem mem_antidiagonalProd (n : α) (s : Finset ι) (f : ι → α) :
  f ∈ antidiagonalProd s n ↔ (∏ i in s, f i = n) ∧ (∀ i, i ∉ s → f i = 1)  := sorry

end CanonicallyOrderedMonoid

theorem Squarefree.cardDistinctFactors_eq_cardFactors {n : ℕ} (hn : Squarefree n) : ω n = Ω n :=
  (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero).mpr hn

namespace Nat

theorem eq_one_of_prod_eq_one {α : Type _} (s : Finset α) (f : α → ℕ) (hp : ∏ i in s, f i = 1) 
    (i : α) (hi : i ∈ s) : f i = 1 := 
  eq_one_of_dvd_one (hp ▸ dvd_prod_of_mem f hi)


theorem fintype_eq_one_of_prod_eq_one {α : Type _} [Fintype α] (f : α → ℕ)
    (hp : ∏ i in Finset.univ, f i = 1) : ∀ i, f i = 1 :=
  fun i => eq_one_of_prod_eq_one univ _ hp i (mem_univ i)

def tuplesWithProd {ι : Type _} [Fintype ι] [DecidableEq ι] (n: ℕ) : Finset (ι → ℕ) := 
    (Fintype.piFinset fun _ : ι => n.divisors).filter fun d => ∏ i, d i = n

@[simp]
theorem mem_tuplesWithProd {ι : Type _} [Fintype ι] [DecidableEq ι] {d: ℕ} {s : ι → ℕ} :
    s ∈ tuplesWithProd d ↔ ∏ i, s i = d ∧ d ≠ 0 :=
  by
  unfold tuplesWithProd
  rw [mem_filter, Fintype.mem_piFinset]
  by_cases hι : Nonempty ι
  swap
  · rw [not_nonempty_iff] at hι
    rw [Fintype.prod_empty]
    exact ⟨fun ⟨_, h⟩ => ⟨h, by linarith⟩, fun ⟨h1d, _⟩ => ⟨by simp, h1d⟩⟩
  simp_rw[mem_divisors]
  constructor
  · exact fun h => ⟨h.2, (h.1 $ Classical.choice hι).2⟩
  · intro h
    simp_rw [←h.1] at *
    exact ⟨fun i => ⟨Finset.dvd_prod_of_mem _ (mem_univ i), h.2⟩, trivial⟩
    
theorem tuplesWithProd_eq  {ι : Type _} [Fintype ι] [DecidableEq ι] (d P: ℕ) (hdP : d ∣ P) (hP : P ≠ 0):
    (tuplesWithProd d : Finset (ι → ℕ)) = 
      (Fintype.piFinset fun _ : ι => P.divisors).filter fun s => ∏ i, s i = d := by
  ext aesop_div
  constructor
  · unfold tuplesWithProd 
    simp_rw [mem_filter, Fintype.mem_piFinset]  
    intro ⟨h, hprod⟩
    simp_rw [mem_divisors] at h
    simp_rw [mem_divisors]
    refine ⟨ fun i => ⟨Trans.trans (h i).1 hdP, hP⟩, hprod⟩ 
  · rw [mem_tuplesWithProd]
    simp_rw [mem_filter, Fintype.mem_piFinset] 
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_of_dvd_ne_zero hP hdP⟩ 
/-
theorem tst {ι R: Type _} [Fintype ι] [DecidableEq ι] [CommSemiring R] 
  (k : ℕ) (f : ι → ArithmeticFunction R) (n : ℕ) :
    (∏ i, f i) n = ∑ a in tuplesWithProd n, ∏ i, f i (a i) := sorry
-/
-- Perhaps there is a better way to do this with partitions, but the proof isn't too bad
-- |{(d1, ..., dh) : d1*...*dh = d}| = h^ω(d) 
theorem card_tuplesWithProd {d : ℕ} (hd : Squarefree d) (h : ℕ) :
    (tuplesWithProd d : Finset (Fin h → ℕ)).card = h ^ ω d := 
  by
  unfold tuplesWithProd
  induction' d using Nat.strong_induction_on with d h_ind
  --apply Nat.strong_induction_on d
  --clear d; intro d
  by_cases h_1 : d = 1
  · rw [h_1];
    rw [show h ^ ω 1 = 1 by
        simp only [eq_self_iff_true, Nat.pow_zero, Nat.ArithmeticFunction.cardDistinctFactors_one]]
    apply card_eq_one.mpr; use fun _ => 1
    ext a; rw [mem_singleton, mem_filter, Fintype.mem_piFinset]; constructor
    · intro h; ext x; apply fintype_eq_one_of_prod_eq_one a h.right
    · intro h; simp [h]
  have := exists_prime_and_dvd h_1
  rcases this with ⟨p, ⟨hp_prime, hp_dvd⟩⟩
  let S : Finset (Fin h → ℕ) := tuplesWithProd d
  let Sp_dvd : Fin h → Finset _ := fun j => S.filter fun s : Fin h → ℕ => p ∣ s j
  have hunion : Finset.univ.biUnion Sp_dvd = S 
  · ext s; rw [mem_biUnion]; constructor
    · rintro ⟨i, _, hi⟩; rw [mem_filter] at hi ; exact hi.1
    intro hs
    rw [mem_tuplesWithProd] at hs 
    rw [← hs.1] at hp_dvd 
    rw [← Finset.toList_toFinset univ, List.prod_toFinset s _, Prime.dvd_prod_iff] at hp_dvd 
    rcases hp_dvd with ⟨si, ⟨hsi, hpsi⟩⟩
    rw [List.mem_map] at hsi 
    rcases hsi with ⟨i, ⟨_, hsi⟩⟩
    use i; constructor; exact mem_univ i
    rw [mem_filter]
    rw [← hsi] at hpsi 
    exact ⟨mem_tuplesWithProd.mpr hs, hpsi⟩
    rw [← Nat.prime_iff]; exact hp_prime
    apply Finset.nodup_toList
  have hdisj :
    ∀ i : Fin h,
      i ∈ (Finset.univ : Finset <| Fin h) →
        ∀ j : Fin h, j ∈ (Finset.univ : Finset <| Fin h) → i ≠ j → Disjoint (Sp_dvd i) (Sp_dvd j) :=
    by
    intro i _ j _ hij
    rw [disjoint_iff_ne]
    intro s hs t ht
    rw [mem_filter, mem_tuplesWithProd] at hs ht 
    by_contra hst
    rw [hst] at hs 
    have : (t i).coprime (t j) := by
      apply coprime_of_squarefree_mul
      apply Squarefree.squarefree_of_dvd _ hd
      calc
        t i * t j ∣ t i * t j * ∏ k in (univ.erase i).erase j, t k :=
          ⟨∏ k in (univ.erase i).erase j, t k, rfl⟩
        _ = t i * ∏ k in univ.erase i, t k :=
          by
          rw [mul_assoc, mul_prod_erase]
          rw [mem_erase]
          exact ⟨ne_comm.mp hij, mem_univ j⟩
        _ = d := by rw [mul_prod_erase _ _ (mem_univ i), hs.1.1]
    apply absurd this
    rw [Nat.Prime.not_coprime_iff_dvd]
    use p; exact ⟨hp_prime, hs.2, ht.2⟩
  dsimp at hunion hdisj
  unfold tuplesWithProd at hunion hdisj
  rw [←hunion]
  rw [Finset.card_biUnion hdisj]
  cases' hp_dvd with k hk
  have hk_dvd : k ∣ d := by use p; rw [mul_comm]; exact hk
  have hp_dvd : p ∣ d := by use k; 
  have hp_ne_zero : p ≠ 0 := ne_zero_of_dvd_ne_zero hd.ne_zero hp_dvd
  have hp_pos : 0 < p := zero_lt_iff.mpr hp_ne_zero
  let f : Fin h → ∀ s : Fin h → ℕ, s ∈ tuplesWithProd k → Fin h → ℕ := fun i s _ => fun j =>
    if i = j then p * s j else s j
  have himg : ∀ (i s) (hs : s ∈ tuplesWithProd k), f i s hs ∈ Sp_dvd i :=
    by
    intro i s hs
    rw [mem_tuplesWithProd] at hs 
    rw [mem_filter, mem_tuplesWithProd]; constructor; constructor
    calc
      ∏ j : Fin h, ite (i = j) (p * s j) (s j) = p * s i * ∏ j in univ.erase i, s j :=
        by
        rw [← mul_prod_erase univ _ (mem_univ i)]
        rw [if_pos rfl]
        apply congr_arg fun x => p * s i * x
        apply prod_congr rfl; intro j hj
        rw [mem_erase, ne_comm] at hj 
        rw [if_neg hj.1]
      _ = d := by rw [mul_assoc, mul_prod_erase _ _ (mem_univ i), hs.1, hk]
    exact hd.ne_zero
    dsimp only []
    rw [if_pos rfl]
    apply dvd_mul_right
  have hinj :
    ∀ (i s t) (hs : s ∈ tuplesWithProd k) (ht : t ∈ tuplesWithProd k),
      f i s hs = f i t ht → s = t :=
    by
    intro i s t hs ht hfst; funext j
    by_cases hij : i = j
    · rw [← mul_right_inj' hp_ne_zero]
      calc
        p * s j = f i s hs j := eq_comm.mp <| if_pos hij
        _ = f i t ht j := by rw [hfst]
        _ = p * t j := if_pos hij
    ·
      calc
        s j = f i s hs j := eq_comm.mp <| if_neg hij
        _ = f i t ht j := by rw [hfst]
        _ = t j := if_neg hij
  have hsurj :
    ∀ (i t) (_ : t ∈ Sp_dvd i), ∃ (s : _) (hs : s ∈ tuplesWithProd k), f i s hs = t :=
    by
    
    intro i t ht
    rw [mem_filter] at ht ; dsimp only []
    dsimp only [] at ht  
    rw [mem_tuplesWithProd] at ht 
    let s j := if i = j then t j / p else t j
    use s; constructor; swap
    rw [mem_tuplesWithProd]; constructor
    dsimp only []
    calc
      ∏ j, ite (i = j) (t j / p) (t j) = t i / p * ∏ j in univ.erase i, t j :=
        by
        rw [← Finset.mul_prod_erase univ s (mem_univ i)]
        dsimp only []; rw [if_pos rfl]
        apply congr_arg fun x => t i / p * x
        apply prod_congr rfl; intro j hj
        rw [mem_erase, ne_comm] at hj 
        rw [if_neg hj.1]
      _ = (t i * ∏ j in univ.erase i, t j) / p :=
        by
        conv =>
          rhs
          rw [mul_comm]
        rw [Nat.mul_div_assoc _ ht.2, mul_comm]
      _ = d / p := by rw [Finset.mul_prod_erase univ t (mem_univ i), ht.1.1]
      _ = k := by rw [hk]; exact Nat.mul_div_cancel_left k hp_pos
    apply ne_zero_of_dvd_ne_zero hd.ne_zero hk_dvd
    funext j
    dsimp only []
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, Nat.mul_div_cancel']
      rw [← hij]; exact ht.2
    · rw [if_neg hij, if_neg hij]
  have hk_sq : Squarefree k := Squarefree.squarefree_of_dvd hk_dvd hd
  calc
    ∑ i, (Sp_dvd i).card = ∑ _i : Fin h, (tuplesWithProd k).card :=
      by
      apply sum_congr rfl; intro i _; rw [eq_comm]
      apply Finset.card_congr (f i) (himg i) (hinj i) (hsurj i)
    _ = h ^ ω d := by
      rw [Fin.sum_const]
      dsimp only [tuplesWithProd]
      rw [h_ind k _ _, smul_eq_mul, ←_root_.pow_succ]
      rw [hd.cardDistinctFactors_eq_cardFactors,
        hk_sq.cardDistinctFactors_eq_cardFactors, ←
        ArithmeticFunction.cardFactors_apply_prime hp_prime, ←
        Nat.ArithmeticFunction.cardFactors_mul, mul_comm, hk]
      exact Squarefree.ne_zero hk_sq; exact Nat.Prime.ne_zero hp_prime
      apply lt_of_le_of_ne; apply le_of_dvd _ hk_dvd; rw [zero_lt_iff]; exact hd.ne_zero
      rw [← one_mul k, hk]; apply Nat.ne_of_lt; apply mul_lt_mul; exact hp_prime.one_lt
      exact le_rfl; rw [zero_lt_iff]; exact Squarefree.ne_zero hk_sq
      exact Nat.zero_le p
      exact hk_sq

theorem nat_lcm_mul_left (a b c : ℕ) : (a * b).lcm (a * c) = a * b.lcm c :=
  by
  rw [← lcm_eq_nat_lcm, lcm_mul_left]
  dsimp; rw [mul_one]
  rw [lcm_eq_nat_lcm]

theorem prod3 (a : Fin 3 → ℕ) : ∏ i, a i = a 0 * a 1 * a 2 :=
  by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
  simp

theorem card_lcm_eq {n : ℕ} (hn : Squarefree n) :
    Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) =
      3 ^ ω n :=
  by
  rw [← card_tuplesWithProd hn 3, eq_comm]
  have hn_ne_zero : n ≠ 0 := Squarefree.ne_zero hn
  let f : ∀ (a : Fin 3 → ℕ) (_ : a ∈ tuplesWithProd n), ℕ × ℕ := fun a _ =>
    (a 0 * a 1, a 0 * a 2)
  have hprod : ∀ (a : Fin 3 → ℕ) (_ : a ∈ tuplesWithProd n), a 0 * a 1 * a 2 = n :=
    by
    intro a ha; rw [mem_tuplesWithProd] at ha 
    rw [← ha.1, prod3 a]
  have ha_ne_zero : ∀ (a : Fin 3 → ℕ) (_ : a ∈ tuplesWithProd n) (i : Fin 3), a i ≠ 0 :=
    by
    intro a ha i; rw [mem_tuplesWithProd] at ha 
    by_contra hai
    rw [Finset.prod_eq_zero (mem_univ i) hai] at ha 
    exact hn_ne_zero (eq_comm.mp ha.1)
  have h_img :
    ∀ (a : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd n),
      f a ha ∈ Finset.filter (fun p : ℕ × ℕ => n = p.fst.lcm p.snd) (n.divisors ×ˢ n.divisors) :=
    by
    intro a ha
    rw [mem_filter, Finset.mem_product, mem_divisors, mem_divisors]
    constructor; constructor; constructor
    calc
      a 0 * a 1 ∣ a 0 * a 1 * a 2 := by use a 2
      _ = n := hprod a ha
    exact hn_ne_zero; constructor
    calc
      a 0 * a 2 ∣ a 0 * a 1 * a 2 := by use a 1; ring
      _ = n := hprod a ha
    exact hn_ne_zero
    dsimp
    rw [nat_lcm_mul_left, Nat.coprime.lcm_eq_mul, ← hprod a ha]
    ring
    apply coprime_of_squarefree_mul
    apply Squarefree.squarefree_of_dvd _ hn
    calc
      a 1 * a 2 ∣ a 0 * a 1 * a 2 := by use a 0; ring
      _ = n := hprod a ha
  have h_inj :
    ∀ (a b : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd n) (hb : b ∈ tuplesWithProd n),
      f a ha = f b hb → a = b :=
    by
    intro a b ha hb hfab
    dsimp only [] at hfab 
    cases' Prod.mk.inj hfab with hfab1 hfab2
    have hab2 : a 2 = b 2 :=
      by
      have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2
      rw [hprod a ha, hfab1, hprod b hb]
      rw [← mul_right_inj']
      exact hprods
      apply mul_ne_zero (ha_ne_zero a ha 0) (ha_ne_zero a ha 1)
    have hab0 : a 0 = b 0 := by
      rw [← mul_left_inj']
      rw [hab2] at hfab2 
      exact hfab2; exact ha_ne_zero b hb 2
    have hab1 : a 1 = b 1 := by
      rw [← mul_right_inj']
      rw [hab0] at hfab1 
      exact hfab1; exact ha_ne_zero b hb 0
    funext i
    fin_cases i
    all_goals assumption
  have h_surj :
    ∀ b : ℕ × ℕ,
      b ∈ Finset.filter (fun p : ℕ × ℕ => n = p.fst.lcm p.snd) (n.divisors ×ˢ n.divisors) →
        ∃ (a : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd n), f a ha = b :=
    by
    intro b hb
    let g := b.fst.gcd b.snd
    let a := fun i : Fin 3 => if i = 0 then g else if i = 1 then b.fst / g else b.snd / g
    have ha : a ∈ tuplesWithProd n :=
      by
      rw [mem_tuplesWithProd]
      rw [mem_filter, Finset.mem_product] at hb 
      constructor
      rw [prod3 a]
      dsimp only []
      have h10 : (1 : Fin 3) ≠ 0 := by rw [Fin.ne_iff_vne]; norm_num
      have h20 : (2 : Fin 3) ≠ 0 := by rw [Fin.ne_iff_vne]; norm_num
      have h21 : (2 : Fin 3) ≠ 1 := by rw [Fin.ne_iff_vne]; norm_num
      rw [if_neg h10, if_pos rfl, if_pos rfl, if_neg h20, if_neg h21, hb.2]
      calc
        g * (b.fst / g) * (b.snd / g) = b.fst * (b.snd / g) := by
          rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _)]
        _ = b.fst * b.snd / g := ?_
      rw [Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
      exact hn.ne_zero
    use a; use ha
    dsimp only []
    rw [if_pos rfl]
    apply Prod.ext
    calc
      (g * if 1 = 0 then g else if 1 = 1 then b.fst / g else b.snd / g) = g * (b.fst / g) := by simp
      _ = b.fst := ?_
    apply Nat.mul_div_cancel' (Nat.gcd_dvd_left b.fst b.snd)
    calc
      (g * if 2 = 0 then g else if 2 = 1 then b.fst / g else b.snd / g) = g * (b.snd / g) := by simp
      _ = b.snd := ?_
    apply Nat.mul_div_cancel' (Nat.gcd_dvd_right b.fst b.snd)
  apply Finset.card_congr f h_img h_inj h_surj


end Nat