/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.Tactic.ExtractGoal
import Mathlib.NumberTheory.ArithmeticFunction
import SelbergSieve.ForArithmeticFunction

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

@[simp]
theorem antidiagonalProd_zero : 
    antidiagonalProd (ι:=ι) 0 = ∅ := by
  ext; simp

theorem antidiagonalProd_empty_one :
    antidiagonalProd (ι:=ι) 1 = {fun _ => 1} := by
  ext f; simp?
  constructor
  · intro hf; ext i; 
    rw [←Nat.dvd_one, ←hf]; 
    apply Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  · intro hf 
    rw [hf]
    simp
theorem antidiagonalProd_empty_of_ne_one [IsEmpty ι] (hn : n ≠ 1) :
    antidiagonalProd (ι:=ι) n = ∅ := by
  ext; simp [hn.symm]

theorem dvd_of_mem_antidiagonalProd {n : ℕ} {f : ι → ℕ} (hf : f ∈ antidiagonalProd n) (i : ι):
    f i ∣ n := by
  rw [←(mem_antidiagonalProd.mp hf).1]
  apply Finset.dvd_prod_of_mem _ (mem_univ i)

theorem ne_zero_of_mem_antidiagonalProd {n : ℕ} {f : ι → ℕ} (hf : f ∈ antidiagonalProd n) (i : ι):
    f i ≠ 0 :=  
  ne_zero_of_dvd_ne_zero (mem_antidiagonalProd.mp hf).2 (dvd_of_mem_antidiagonalProd hf i)

theorem prod_eq_of_mem_antidiagonalProd {n : ℕ} {f : ι → ℕ} (hf : f ∈ antidiagonalProd n):
    ∏ i, f i = n :=  
  (mem_antidiagonalProd.mp hf).1

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

lemma filter_factors {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    n.factors.toFinset.filter fun p => p ∣ m = m.factors.toFinset := by 
  ext p
  simp_rw [mem_filter, List.mem_toFinset]
  rw [mem_factors hn, mem_factors (ne_zero_of_dvd_ne_zero hn hmn)]
  exact ⟨(by tauto), fun ⟨hp, hpm⟩ => ⟨⟨hp, Trans.trans hpm hmn⟩, hpm⟩⟩

lemma antidiagonalProd_exists_unique_prime_dvd {n p : ℕ} (hn : Squarefree n) 
    (hp : p ∈ n.factors) (f : ι → ℕ) (hf : f ∈ antidiagonalProd n) :
    ∃! i, p ∣ f i := by 
  rw [mem_antidiagonalProd] at hf
  rw [mem_factors hf.2, ← hf.1, hp.1.prime.dvd_finset_prod_iff] at hp
  obtain ⟨i, _, hi⟩ := hp.2
  use i
  refine ⟨hi, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj⟩
  apply Nat.coprime_of_squarefree_mul
  apply hn.squarefree_of_dvd
  rw [←hf.1, ←Finset.mul_prod_erase _ _ (mem_univ i),
    ←Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij, mem_univ j⟩), ←mul_assoc]
  apply Nat.dvd_mul_right

private def bij (n : ℕ) : ∀ f (_ : f ∈ n.factors.toFinset.pi fun _ => (univ: Finset ι)),  ι → ℕ := 
    fun f _ i => ∏ p in Finset.filter (fun p => f p.1 p.2 = i) n.factors.toFinset.attach,  p

private theorem bij_img (n : ℕ) (hn : Squarefree n)
  (f : (p : ℕ) → p ∈ List.toFinset (factors n) → ι) (hf : f ∈ pi (List.toFinset (factors n)) fun _ => univ) :
    Nat.bij n f hf ∈ antidiagonalProd n := by
  rw [mem_antidiagonalProd]
  refine ⟨?_, hn.ne_zero⟩
  simp_rw [Nat.bij, List.mem_toFinset, ←prod_filter, prod_fiberwise]
  rw [prod_attach (f := fun x => x)]
  apply prod_factors_toFinset_of_squarefree hn

private theorem bij_inj (n : ℕ) (hn : Squarefree n)
    (f g : (p : ℕ) → p ∈ List.toFinset (factors n) → ι) (hf : f ∈ pi (List.toFinset (factors n)) fun _ => univ)
    (hg : g ∈ pi (List.toFinset (factors n)) fun _ => univ) : Nat.bij n f hf = Nat.bij n g hg → f = g := by
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.bij]
  apply ne_of_mem_of_not_mem (s:= ({x | (p ∣ x)}:Set ℕ)) <;> simp_rw [Set.mem_setOf_eq]
  · rw [Finset.prod_filter]
    convert Finset.dvd_prod_of_mem _ (mem_attach (n.factors.toFinset) ⟨p, hp⟩)
    rw [if_pos rfl]
  · rw [List.mem_toFinset, Nat.mem_factors hn.ne_zero] at hp
    rw [Prime.dvd_finset_prod_iff hp.1.prime]
    push_neg
    intro q hq
    rw [Nat.prime_dvd_prime_iff_eq hp.1 (Nat.prime_of_mem_factors $ List.mem_toFinset.mp q.2)]
    intro hpq; subst hpq
    rw [(mem_filter.mp hq).2] at hfg
    exact hfg rfl

private theorem bij_surj (n : ℕ) (hn : Squarefree n)
    (t : ι → ℕ) (ht : t ∈ antidiagonalProd n) : ∃ g hg, Nat.bij n g hg = t := by
  have exists_unique := fun (p : ℕ) (hp : p ∈ n.factors.toFinset) => 
    (antidiagonalProd_exists_unique_prime_dvd hn (List.mem_toFinset.mp hp) t ht)
  choose f hf hf_unique using exists_unique
  use f
  simp only [mem_pi, mem_univ, implies_true, forall_const, exists_true_left]
  funext i
  trans (∏ p in n.factors.toFinset.attach, if p.1 ∣ t i then p else 1)
  · rw [Nat.bij, ←prod_filter]
    congr
    ext p
    constructor
    · intro h; rw [←h]; apply hf
    · exact fun h => (hf_unique p p.2 i h).symm
  rw [prod_attach (f:=fun p => if p ∣ t i then p else 1), ←Finset.prod_filter]
  have : t i ∣ n
  · apply dvd_of_mem_antidiagonalProd ht
  rw [filter_factors this hn.ne_zero]
  apply prod_factors_toFinset_of_squarefree $ hn.squarefree_of_dvd this

theorem card_antidiagonalProd_pi (n : ℕ) (hn : Squarefree n) : 
    (n.factors.toFinset.pi (fun _ => (univ : Finset ι))).card = 
      (antidiagonalProd n : Finset (ι → ℕ)).card := 
  Finset.card_congr (bij n) (Nat.bij_img n hn) (Nat.bij_inj n hn) (Nat.bij_surj n hn)

theorem card_antidiagonalProd {d : ℕ} (hd : Squarefree d) (k : ℕ) :
    (antidiagonalProd d : Finset (Fin k → ℕ)).card = k ^ ω d := by
  rw [←card_antidiagonalProd_pi d hd, Finset.card_pi, Finset.prod_const, card_fin]
  congr

theorem nat_lcm_mul_left (a b c : ℕ) : (a * b).lcm (a * c) = a * b.lcm c :=
  by
  rw [← lcm_eq_nat_lcm, lcm_mul_left]
  dsimp; rw [mul_one]
  rw [lcm_eq_nat_lcm]

@[reducible]
private def f : ∀ (a : Fin 3 → ℕ) (_ : a ∈ antidiagonalProd n), ℕ × ℕ := fun a _ =>
    (a 0 * a 1, a 0 * a 2) 

private theorem antidiagonalProd_three : ∀ (a : Fin 3 → ℕ) (_ : a ∈ antidiagonalProd n), a 0 * a 1 * a 2 = n := by
    intro a ha
    rw [← (mem_antidiagonalProd.mp ha).1, Fin.prod_univ_three a]

private theorem f_img {n : ℕ} (hn : Squarefree n) : ∀ (a : Fin 3 → ℕ) (ha : a ∈ antidiagonalProd n),
      f a ha ∈ Finset.filter (fun p : ℕ × ℕ => n = p.fst.lcm p.snd) (n.divisors ×ˢ n.divisors) := by
  intro a ha
  rw [mem_filter, Finset.mem_product, mem_divisors, mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ←antidiagonalProd_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  rw [nat_lcm_mul_left, Nat.coprime.lcm_eq_mul]
  · ring
  refine coprime_of_squarefree_mul (hn.squarefree_of_dvd ?_)
  use a 0; rw [←antidiagonalProd_three a ha]; ring

private theorem f_inj {n : ℕ} :
    ∀ (a b : Fin 3 → ℕ) (ha : a ∈ antidiagonalProd n) (hb : b ∈ antidiagonalProd n),
      f a ha = f b hb → a = b := by
  intro a b ha hb hfab
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab 
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2
  · rw [antidiagonalProd_three a ha, hfab1, antidiagonalProd_three b hb]
  have hab2 : a 2 = b 2
  · rw [← mul_right_inj' $ mul_ne_zero (ne_zero_of_mem_antidiagonalProd ha 0) 
      (ne_zero_of_mem_antidiagonalProd ha 1)]
    exact hprods
  have hab0 : a 0 = b 0
  · rw [hab2] at hfab2 
    exact (mul_left_inj' $ ne_zero_of_mem_antidiagonalProd hb 2).mp hfab2;
  have hab1 : a 1 = b 1
  · rw [hab0] at hfab1 
    exact (mul_right_inj' $ ne_zero_of_mem_antidiagonalProd hb 0).mp hfab1; 
  funext i; fin_cases i <;> assumption

private theorem f_surj {n : ℕ} (hn : n ≠ 0) : 
    ∀ b : ℕ × ℕ,
      b ∈ Finset.filter (fun p : ℕ × ℕ => n = p.fst.lcm p.snd) (n.divisors ×ˢ n.divisors) →
        ∃ (a : Fin 3 → ℕ) (ha : a ∈ antidiagonalProd n), f a ha = b := by
  intro b hb
  let g := b.fst.gcd b.snd
  let a := fun i : Fin 3 => if i = 0 then g else if i = 1 then b.fst / g else b.snd / g
  have ha : a ∈ antidiagonalProd n := by
    rw [mem_antidiagonalProd]
    rw [mem_filter, Finset.mem_product] at hb 
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      simp_rw [ite_true, ite_false]
      rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _), hb.2, lcm, 
        Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
  use a; use ha
  apply Prod.ext <;> simp_rw [ite_true, ite_false] <;> apply Nat.mul_div_cancel'
  · apply Nat.gcd_dvd_left 
  · apply Nat.gcd_dvd_right

theorem card_lcm_eq {n : ℕ} (hn : Squarefree n) :
    Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) =
      3 ^ ω n := by
  rw [← card_antidiagonalProd hn 3, eq_comm]
  apply Finset.card_congr f (f_img hn) (f_inj) (f_surj hn.ne_zero)


end Nat