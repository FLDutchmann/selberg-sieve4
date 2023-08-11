/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.ArithmeticFunction

open Nat Nat.ArithmeticFunction BigOperators Finset


/-
namespace CanonicallyOrderedMonoid
variable {α : Type u} {ι : Type v} [DecidableEq α] [DecidableEq ι] [CanonicallyOrderedMonoid α] 

@[to_additive]
noncomputable local instance : DecidablePred fun n : α => Set.Finite (Set.Iic n) :=
  Classical.decPred _

@[to_additive]
noncomputable def antidiagonalProd (s : Finset ι) (n : α)  : Finset (ι → α) :=
  Finset.filter (fun f => (∏ d in s, f d) = n)
    ((s.pi (fun _ => if h : Set.Finite (Set.Iic n) then 
        haveI : Fintype (Set.Iic n) := Set.Finite.fintype h
        Set.toFinset (Set.Iic n) else ∅)).map 
      (⟨fun f i => if h : i ∈ s then f i h else 1, 
        fun f g h => by ext i hi; simpa [dif_pos hi] using congr_fun h i⟩))
  /-
  if 
    h : Set.Finite (Set.Iic n) 
  then 
    haveI : Fintype (Set.Iic n) := Set.Finite.fintype h
    Finset.filter (fun f => (∏ d in s, f d) = n)
      ((s.pi (fun _ => Set.toFinset (Set.Iic n))).map 
        (⟨fun f i => if h : i ∈ s then f i h else 1, 
          fun f g h => by ext i hi; simpa [dif_pos hi] using congr_fun h i⟩))
  else 
    if s = ∅ then {fun _ => 1} else ∅ -/


theorem mem_antidiagonalProd_of_finite (n : α) (s : Finset ι) (f : ι → α) (hn : Set.Finite (Set.Iic n)) :
    f ∈ antidiagonalProd s n ↔ (∏ i in s, f i = n) ∧ (∀ i, i ∉ s → f i = 1) := by
  unfold antidiagonalProd
  rw [dif_pos hn]
  rw [mem_filter]
  simp only [mem_map, mem_pi, Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨ ⟨g, _, hgf⟩, hfprod⟩
    constructor
    · exact hfprod
    · intro i hi
      obtain hgfi := congrFun hgf i
      rw [dif_neg hi] at hgfi
      exact hgfi.symm
  · intro ⟨hprod, hf⟩
    constructor
    · use fun i _ => f i
      constructor
      · intro i hi
        --have : Fintype (Set.Iic n) := @Set.Finite.fintype α (Set.Iic n) h 
        convert (Set.mem_toFinset).mpr _
        rw [Set.mem_Iic]
        rw [←hprod, ←Finset.prod_erase_mul s f hi]
        exact le_mul_self
      · ext i
        by_cases hi : i ∈ s
        · rw [dif_pos hi]
        · rw [dif_neg hi, hf i hi]
    · exact hprod


theorem mem_antidiagonalProd_of_empty (n : α) (s : Finset ι) (f : ι → α) (hs : s = ∅) :
    f ∈ antidiagonalProd s n ↔ (n = 1) ∧ (∀ i, f i = 1) := by
  unfold antidiagonalProd
  simp only [hs, prod_empty, not_mem_empty, dite_false, mem_map, mem_pi, Function.Embedding.coeFn_mk, exists_and_right,
    and_imp, forall_exists_index, forall_apply_eq_imp_iff₂, mem_filter, not_false_eq_true, forall_true_left] 
  constructor
  · intro ⟨⟨_, hf⟩, hn⟩
    exact ⟨hn.symm, congrFun hf.symm⟩
  · intro ⟨hn, hf⟩; 
    simp [hn]
    constructor
    · use fun _ _ => 1
      intro i hi
      rw [hs] at hi; contradiction
    ext i; exact (hf i).symm

theorem mem_antidiagonalProd (n : α) (s : Finset ι) (f : ι → α) :
    f ∈ antidiagonalProd s n ↔ (∏ i in s, f i = n) ∧ (∀ i, i ∉ s → f i = 1) ∧ (s = ∅ ∨ Set.Finite (Set.Iic n)) := by
  --unfold antidiagonalProd
  by_cases hn : Set.Finite (Set.Iic n)
  · have := mem_antidiagonalProd_of_finite n s f hn
    tauto
  by_cases hs : s = ∅
  · have := mem_antidiagonalProd_of_empty n s f hs
    rw [this]
    simp [hs]
    exact fun _ => eq_comm
  simp [hn, hs]
  unfold antidiagonalProd
  rw [dif_neg hn]
  simp only [mem_filter, mem_map, mem_pi, not_mem_empty, Function.Embedding.coeFn_mk, exists_and_left, and_imp,
    forall_exists_index, mem_filter]
  push_neg
  intro ⟨h, _⟩
  exfalso
  exact hs (Finset.eq_empty_of_forall_not_mem h)

end CanonicallyOrderedMonoid

namespace Nat

instance (α : Type u) [Monoid α] [inst : DecidableRel fun (a b : α) => Associated a b] : DecidableEq (Associates α) := 
  @Quotient.decidableEq _ _ inst


example : (Associates.mk (4:ℕ) = (Associates.mk 2 * Associates.mk (2:ℕ))) := by decide
/-
instance : DecidableRel fun (a b : ℕ) => Associated a b := by
  exact instDecidableRelAssociatedToMonoidToMonoidWithZero
-/
open CanonicallyOrderedMonoid

variable (ι : Type u) [DecidableEq ι]

noncomputable def Nat.Associates.eqiuv : ℕ ≃ Associates ℕ :=
  haveI inst : DecidableRel fun (a b : ℕ) => Associated a b := inferInstance
  ⟨ Associates.mk,
    fun n => @Quotient.rep ℕ (Associated.setoid ℕ) inst _ n,
    by intro x; simp; sorry,
    by intro x; simp; sorry ⟩

instance : Infinite (Associates ℕ) := sorry

theorem lemma0 : Set.Iic (0 : Associates ℕ) = Set.univ := by
  ext d; simp_rw [Set.mem_Iic, Set.mem_univ, iff_true]; use 0; rw [mul_zero]

theorem tmp (n : Associates ℕ):
    Set.Finite (Set.Iic n) ↔ n ≠ 0 := by
  constructor
  · contrapose!
    intro hn
    rw [hn, lemma0, ←Set.Infinite]
    apply Set.infinite_univ
  · intro hn
    obtain ⟨k, hk⟩ := Associates.exists_rep n
    --rw [←Set.finite_coe_iff]
    apply Set.Finite.ofFinset (image Associates.mk k.divisors )
    simp_rw [Set.mem_Iic, mem_image, mem_divisors]

theorem mem_antidiagonalProd (n : Associates ℕ) (s : Finset ι) (f : ι → Associates ℕ) :
    f ∈ antidiagonalProd s n ↔ (∏ i in s, f i = n) ∧ (∀ i, i ∉ s → f i = 1) ∧ n ≠ 0 := by
  sorry 

theorem mem_antidiagonalProd_univ [Fintype ι] (n : Associates ℕ) (f : ι → Associates ℕ) :
    f ∈ antidiagonalProd univ n ↔ (∏ i, f i = n) ∧ n ≠ 0 := by
  sorry

-/

theorem Squarefree.cardDistinctFactors_eq_cardFactors {n : ℕ} (hn : Squarefree n) : ω n = Ω n :=
  (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero).mpr hn

namespace Nat

theorem eq_one_of_prod_eq_one {α : Type _} (s : Finset α) (f : α → ℕ) (hp : ∏ i in s, f i = 1) 
    (i : α) (hi : i ∈ s) : f i = 1 := 
  eq_one_of_dvd_one (hp ▸ dvd_prod_of_mem f hi)


theorem fintype_eq_one_of_prod_eq_one {α : Type _} [Fintype α] (f : α → ℕ)
    (hp : ∏ i in Finset.univ, f i = 1) : ∀ i, f i = 1 :=
  fun i => eq_one_of_prod_eq_one univ _ hp i (mem_univ i)

variable {ι : Type _} [Fintype ι] [DecidableEq ι] 

def antidiagonalProd (n : ℕ) : Finset (ι → ℕ) := 
    (Fintype.piFinset fun _ : ι => n.divisors).filter fun d => ∏ i, d i = n

@[simp]
theorem mem_antidiagonalProd {d : ℕ} {s : ι → ℕ} :
    s ∈ antidiagonalProd d ↔ ∏ i, s i = d ∧ d ≠ 0 :=
  by
  unfold antidiagonalProd
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
    
theorem antidiagonalProd_eq (d P: ℕ) (hdP : d ∣ P) (hP : P ≠ 0):
    antidiagonalProd d = 
      (Fintype.piFinset fun _ : ι => P.divisors).filter fun s => ∏ i, s i = d := by
  ext _
  constructor
  · unfold antidiagonalProd 
    simp_rw [mem_filter, Fintype.mem_piFinset]  
    intro ⟨h, hprod⟩
    simp_rw [mem_divisors] at h
    simp_rw [mem_divisors]
    refine ⟨ fun i => ⟨Trans.trans (h i).1 hdP, hP⟩, hprod⟩ 
  · rw [mem_antidiagonalProd]
    simp_rw [mem_filter, Fintype.mem_piFinset] 
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_of_dvd_ne_zero hP hdP⟩ 

def antidiagonalProdFilterDvd (n p: ℕ) (i : ι) : Finset (ι → ℕ) := 
  (antidiagonalProd n).filter fun f => p ∣ f i

theorem mem_antidiagonalProdFilterDvd (n p : ℕ) (i : ι) (f : ι → ℕ) :
    f ∈ antidiagonalProdFilterDvd n p i ↔ p ∣ f i ∧ ∏ i, f i = n ∧ n ≠ 0 := by
  unfold antidiagonalProdFilterDvd
  rw [mem_filter, mem_antidiagonalProd]; tauto


theorem union_univ_antidiagonalProdFilterDvd {n p: ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    Finset.univ.biUnion (antidiagonalProdFilterDvd n p) = (antidiagonalProd n : Finset (ι → ℕ)) := by
  ext s; simp_rw [mem_biUnion, mem_antidiagonalProdFilterDvd, mem_antidiagonalProd]; 
  constructor
  · intro _; tauto
  intro hs
  rw [←hs.1, ←Finset.toList_toFinset univ, List.prod_toFinset s (Finset.nodup_toList _), 
    hp.prime.dvd_prod_iff] at hpn 
  · obtain ⟨si, ⟨hsi, hpsi⟩⟩ := hpn
    rw [List.mem_map] at hsi 
    obtain ⟨i, ⟨_, hsi⟩⟩ := hsi 
    use i; rw [hsi]
    exact ⟨mem_univ i, hpsi, hs⟩

theorem antidiagonalProdFilterDvd_disjoint {n p : ℕ} {i j : ι} (hn : Squarefree n) (hp : p.Prime) 
    (hij : i ≠ j) : 
    Disjoint (antidiagonalProdFilterDvd n p i) (antidiagonalProdFilterDvd n p j) := by
  rw [disjoint_iff_ne]
  intro s hs t ht
  rw [mem_antidiagonalProdFilterDvd] at hs ht 
  by_contra hst
  rw [hst] at hs 
  have : (t i).coprime (t j) := by
    apply coprime_of_squarefree_mul
    apply hn.squarefree_of_dvd
    calc
      t i * t j ∣ t i * t j * ∏ k in (univ.erase i).erase j, t k :=
        ⟨∏ k in (univ.erase i).erase j, t k, rfl⟩
      _ = t i * ∏ k in univ.erase i, t k :=
        by
        rw [mul_assoc, mul_prod_erase]
        rw [mem_erase]
        exact ⟨ne_comm.mp hij, mem_univ j⟩
      _ = n := by rw [mul_prod_erase _ _ (mem_univ i), hs.2.1]
  apply absurd this
  rw [Nat.Prime.not_coprime_iff_dvd]
  use p; exact ⟨hp, hs.1, ht.1⟩

namespace antidiagonalProd

def mulIndex (n p : ℕ) (i : ι) (f : ι → ℕ) (_ : f ∈ antidiagonalProd n) : 
    ι → ℕ :=
  fun j => if i = j then p * f j else f j


theorem mulIndex_image {n p : ℕ} (hzero : p*n ≠ 0) (i : ι) : 
    ∀ f hf, mulIndex n p i f hf ∈ antidiagonalProdFilterDvd (p*n) p i := by 
  intro f hf
  rw [mem_antidiagonalProd] at hf 
  unfold mulIndex
  rw [mem_antidiagonalProdFilterDvd, if_pos rfl]
  refine ⟨dvd_mul_right _ _, ?_, hzero⟩
  · calc
      ∏ j : ι, ite (i = j) (p * f j) (f j) = p * f i * ∏ j in univ.erase i, f j := by
        rw [← mul_prod_erase univ _ (mem_univ i), if_pos rfl]
        congr 1
        exact prod_congr rfl fun j hj => if_neg (Ne.symm (Iff.mp mem_erase hj).left)
      _ = p*n := by rw [mul_assoc, mul_prod_erase _ _ (mem_univ i), hf.1]

theorem mulIndex_injective {n p : ℕ} (hp : p ≠ 0) (i : ι) : 
    ∀ f g hf hg, mulIndex n p i f hf = mulIndex n p i g hg → f = g := by
  intro f g hf hg hfg; funext j
  by_cases hij : i = j
  · rw [← mul_right_inj' hp]
    calc
      p * f j = mulIndex n p i f hf j := (if_pos hij).symm
      _ = mulIndex n p i g hg j := by rw [hfg]
      _ = p * g j := if_pos hij
  · calc
      f j = mulIndex n p i f hf j := (if_neg hij).symm
      _ = mulIndex n p i g hg j := by rw [hfg]
      _ = g j := if_neg hij

theorem mulIndex_surjective {n p : ℕ} (i : ι) 
    (f : ι → ℕ) (hf : f ∈ antidiagonalProdFilterDvd (p*n) p i) : 
    ∃ g hg, mulIndex n p i g hg = f := by

  rw [mem_antidiagonalProdFilterDvd, mul_ne_zero_iff] at hf; dsimp only []
  use fun j => if i = j then f j / p else f j; constructor; swap
  rw [mem_antidiagonalProd]; constructor
  · calc
      ∏ j, ite (i = j) (f j / p) (f j) = f i / p * ∏ j in univ.erase i, f j :=
        by
        rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
        dsimp only []; rw [if_pos rfl]
        congr 1
        apply prod_congr rfl; intro j hj
        rw [mem_erase, ne_comm] at hj 
        rw [if_neg hj.1]
      _ = (f i * ∏ j in univ.erase i, f j) / p :=
        by
        conv =>
          rhs
          rw [mul_comm]
        rw [Nat.mul_div_assoc _ hf.1, mul_comm]
      _ = (p*n) / p := by rw [Finset.mul_prod_erase univ f (mem_univ i), hf.2.1]
      _ = n := by exact Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hf.2.2.1)
  apply hf.2.2.2
  funext j
  unfold mulIndex
  by_cases hij : i = j
  · simp_rw [if_pos hij]; rw [Nat.mul_div_cancel' (hij ▸ hf.1)]
  · simp_rw [if_neg hij]

end antidiagonalProd

open antidiagonalProd in
/-
theorem tst {ι R: Type _} [Fintype ι] [DecidableEq ι] [CommSemiring R] 
  (k : ℕ) (f : ι → ArithmeticFunction R) (n : ℕ) :
    (∏ i, f i) n = ∑ a in antidiagonalProd n, ∏ i, f i (a i) := sorry
-/
-- Perhaps there is a better way to do this with partitions, but the proof isn't too bad
-- |{(d1, ..., dh) : d1*...*dh = d}| = h^ω(d) 
theorem card_antidiagonalProd {d : ℕ} (hd : Squarefree d) (h : ℕ) :
    (antidiagonalProd d : Finset (Fin h → ℕ)).card = h ^ ω d := 
  by
  unfold antidiagonalProd
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
  let S : Finset (Fin h → ℕ) := antidiagonalProd d
  let Sp_dvd : Fin h → Finset _ := antidiagonalProdFilterDvd d p
  have hunion : Finset.univ.biUnion Sp_dvd = S := union_univ_antidiagonalProdFilterDvd hp_prime hp_dvd
  have hdisj :
    ∀ i : Fin h,
      i ∈ (Finset.univ : Finset <| Fin h) →
        ∀ j : Fin h, j ∈ (Finset.univ : Finset <| Fin h) → i ≠ j → Disjoint (Sp_dvd i) (Sp_dvd j) :=
    by
    intro i _ j _ hij
    exact antidiagonalProdFilterDvd_disjoint hd hp_prime hij
  dsimp at hunion hdisj
  unfold antidiagonalProd at hunion hdisj
  rw [←hunion]
  rw [Finset.card_biUnion (hdisj)]
  cases' hp_dvd with k hk
  have hk_dvd : k ∣ d := by use p; rw [mul_comm]; exact hk
  let f := mulIndex (ι := Fin h) k p
  have himg : ∀ (i s) (hs : s ∈ antidiagonalProd k), f i s hs ∈ antidiagonalProdFilterDvd d p i :=
    by exact hk.symm ▸ (antidiagonalProd.mulIndex_image (ι := Fin h) (hk ▸ hd.ne_zero)) 
  have hinj :
    ∀ (i s t) (hs : s ∈ antidiagonalProd k) (ht : t ∈ antidiagonalProd k),
      f i s hs = f i t ht → s = t := mulIndex_injective hp_prime.ne_zero
  have hsurj :
    ∀ (i t) (_ : t ∈ Sp_dvd i), ∃ (s : _) (hs : s ∈ antidiagonalProd k), f i s hs = t := by
    apply hk.symm ▸ mulIndex_surjective (ι := Fin h)
  
  have hk_sq : Squarefree k := hd.squarefree_of_dvd hk_dvd
  calc
    ∑ i, (Sp_dvd i).card = ∑ _i : Fin h, (antidiagonalProd k).card :=
      by
      apply sum_congr rfl; intro i _; rw [eq_comm]
      apply Finset.card_congr (f i) (himg i) (hinj i) (hsurj i)
    _ = h ^ ω d := by
      rw [Fin.sum_const]
      dsimp only [antidiagonalProd]
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
  rw [← card_antidiagonalProd hn 3, eq_comm]
  have hn_ne_zero : n ≠ 0 := Squarefree.ne_zero hn
  let f : ∀ (a : Fin 3 → ℕ) (_ : a ∈ antidiagonalProd n), ℕ × ℕ := fun a _ =>
    (a 0 * a 1, a 0 * a 2)
  have hprod : ∀ (a : Fin 3 → ℕ) (_ : a ∈ antidiagonalProd n), a 0 * a 1 * a 2 = n :=
    by
    intro a ha; rw [mem_antidiagonalProd] at ha 
    rw [← ha.1, prod3 a]
  have ha_ne_zero : ∀ (a : Fin 3 → ℕ) (_ : a ∈ antidiagonalProd n) (i : Fin 3), a i ≠ 0 :=
    by
    intro a ha i; rw [mem_antidiagonalProd] at ha 
    by_contra hai
    rw [Finset.prod_eq_zero (mem_univ i) hai] at ha 
    exact hn_ne_zero (eq_comm.mp ha.1)
  have h_img :
    ∀ (a : Fin 3 → ℕ) (ha : a ∈ antidiagonalProd n),
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
    ∀ (a b : Fin 3 → ℕ) (ha : a ∈ antidiagonalProd n) (hb : b ∈ antidiagonalProd n),
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
        ∃ (a : Fin 3 → ℕ) (ha : a ∈ antidiagonalProd n), f a ha = b :=
    by
    intro b hb
    let g := b.fst.gcd b.snd
    let a := fun i : Fin 3 => if i = 0 then g else if i = 1 then b.fst / g else b.snd / g
    have ha : a ∈ antidiagonalProd n :=
      by
      rw [mem_antidiagonalProd]
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