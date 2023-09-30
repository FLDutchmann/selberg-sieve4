/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.ArithmeticFunction

open Nat Nat.ArithmeticFunction BigOperators Finset

variable {α : Type u} {ι : Type v} [DecidableEq α] [DecidableEq ι] [CommMonoid α] 

namespace Set

def productsAntidiagonal (s : Finset ι) (n : α)  : Set (ι → α) := 
  { f : ι → α | ∏ i in s, f i = n ∧ ∀ i, i ∉ s → f i = 1 }

@[simp]
theorem mem_productsAntidiagonal {s : Finset ι} {n : α} {f : ι → α} : 
    f ∈ productsAntidiagonal s n ↔ ∏ i in s, f i = n ∧ ∀ i, i ∉ s → f i = 1 := by
  simp [productsAntidiagonal]

theorem prod_eq_of_mem_productsAntidiagonal {s : Finset ι} {n : α} {f : ι → α} 
    (hf : f ∈ productsAntidiagonal s n) :
    ∏ i in s, f i = n := by
  exact (mem_productsAntidiagonal.mp hf).1

theorem dvd_of_mem_productsAntidiagonal {s : Finset ι} {n : α} {f : ι → α} 
    (hf : f ∈ productsAntidiagonal s n) (i : ι) : 
    f i ∣ n := by
  rw [mem_productsAntidiagonal] at hf 
  by_cases hi : i ∈ s
  · rw [←hf.1]; exact dvd_prod_of_mem f hi
  · rw [hf.2 i hi]; exact one_dvd _

end Set

namespace Finset 

open Classical in
noncomputable def productsAntidiagonal (s : Finset ι) (n : α)  : Finset (ι → α) := 
  if h : (Set.productsAntidiagonal s n).Finite then
    h.toFinset
  else ∅

theorem mem_productsAntidiagonal_of_finite {s : Finset ι} {n : α} {f : ι → α}
    (h : (Set.productsAntidiagonal s n).Finite) :
    f ∈ productsAntidiagonal s n ↔ ∏ i in s, f i = n ∧ (∀ i, i ∉ s → f i = 1) := by
  unfold productsAntidiagonal
  rw [dif_pos h, Set.Finite.mem_toFinset, Set.mem_productsAntidiagonal]

theorem productsAntidiagonal_of_infinite {s : Finset ι} {n : α}
    (h : (Set.productsAntidiagonal s n).Infinite) :
    productsAntidiagonal s n = ∅ := by
  unfold productsAntidiagonal
  rw [dif_neg h]

theorem mem_productsAntidiagonal {s : Finset ι} {n : α} {f : ι → α} : 
    f ∈ productsAntidiagonal s n ↔ ∏ i in s, f i = n ∧ (∀ i, i ∉ s → f i = 1) 
      ∧ Set.Finite (Set.productsAntidiagonal s n) := by
  by_cases h : Set.Finite (Set.productsAntidiagonal s n)
  · have test := mem_productsAntidiagonal_of_finite h (f:=f)
    tauto
  · rw [productsAntidiagonal_of_infinite h]; tauto
  
end Finset

/-
namespace CanonicallyOrderedMonoid
variable {α : Type u} {ι : Type v} [DecidableEq α] [DecidableEq ι] [CanonicallyOrderedMonoid α] 

@[to_additive]
noncomputable local instance : DecidablePred fun n : α => Set.Finite (Set.Iic n) :=
  Classical.decPred _

@[to_additive]
noncomputable def productsAntidiagonal (s : Finset ι) (n : α)  : Finset (ι → α) :=
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


theorem mem_productsAntidiagonal_of_finite (n : α) (s : Finset ι) (f : ι → α) (hn : Set.Finite (Set.Iic n)) :
    f ∈ productsAntidiagonal s n ↔ (∏ i in s, f i = n) ∧ (∀ i, i ∉ s → f i = 1) := by
  unfold productsAntidiagonal
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


theorem mem_productsAntidiagonal_of_empty (n : α) (s : Finset ι) (f : ι → α) (hs : s = ∅) :
    f ∈ productsAntidiagonal s n ↔ (n = 1) ∧ (∀ i, f i = 1) := by
  unfold productsAntidiagonal
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

theorem mem_productsAntidiagonal (n : α) (s : Finset ι) (f : ι → α) :
    f ∈ productsAntidiagonal s n ↔ (∏ i in s, f i = n) ∧ (∀ i, i ∉ s → f i = 1) ∧ (s = ∅ ∨ Set.Finite (Set.Iic n)) := by
  --unfold productsAntidiagonal
  by_cases hn : Set.Finite (Set.Iic n)
  · have := mem_productsAntidiagonal_of_finite n s f hn
    tauto
  by_cases hs : s = ∅
  · have := mem_productsAntidiagonal_of_empty n s f hs
    rw [this]
    simp [hs]
    exact fun _ => eq_comm
  simp [hn, hs]
  unfold productsAntidiagonal
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

theorem mem_productsAntidiagonal (n : Associates ℕ) (s : Finset ι) (f : ι → Associates ℕ) :
    f ∈ productsAntidiagonal s n ↔ (∏ i in s, f i = n) ∧ (∀ i, i ∉ s → f i = 1) ∧ n ≠ 0 := by
  sorry 

theorem mem_productsAntidiagonal_univ [Fintype ι] (n : Associates ℕ) (f : ι → Associates ℕ) :
    f ∈ productsAntidiagonal univ n ↔ (∏ i, f i = n) ∧ n ≠ 0 := by
  sorry

-/

-- theorem Squarefree.cardDistinctFactors_eq_cardFactors {n : ℕ} (hn : Squarefree n) : ω n = Ω n :=
--   (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero).mpr hn

namespace Nat

-- theorem eq_one_of_prod_eq_one {α : Type _} (s : Finset α) (f : α → ℕ) (hp : ∏ i in s, f i = 1) 
--     (i : α) (hi : i ∈ s) : f i = 1 := 
--   eq_one_of_dvd_one (hp ▸ dvd_prod_of_mem f hi)

-- theorem fintype_eq_one_of_prod_eq_one {α : Type _} [Fintype α] (f : α → ℕ)
--     (hp : ∏ i in Finset.univ, f i = 1) : ∀ i, f i = 1 :=
--   fun i => eq_one_of_prod_eq_one univ _ hp i (mem_univ i)

open Finset

variable {ι : Type _} [Fintype ι] [DecidableEq ι] 

def productsAntidiagonal (n : ℕ) : Finset (ι → ℕ) := 
    (Fintype.piFinset fun _ : ι => n.divisors).filter fun d => ∏ i, d i = n

@[simp]
theorem mem_productsAntidiagonal {d : ℕ} {f : ι → ℕ} :
    f ∈ productsAntidiagonal d ↔ ∏ i , f i = d ∧ d ≠ 0 := by
  unfold productsAntidiagonal
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
theorem productsAntidiagonal_zero : 
    productsAntidiagonal (ι:=ι) 0 = ∅ := by
  ext; simp

theorem productsAntidiagonal_one :
    productsAntidiagonal (ι:=ι) 1 = {fun _ => 1} := by
  ext f; simp only [mem_productsAntidiagonal, and_true, mem_singleton]
  constructor
  · intro hf; ext i; 
    rw [←Nat.dvd_one, ←hf]; 
    apply Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  · intro hf 
    rw [hf]
    simp
  
theorem productsAntidiagonal_empty_of_ne_one [IsEmpty ι] (hn : n ≠ 1) :
    productsAntidiagonal (ι:=ι) n = ∅ := by
  ext; simp [hn.symm]

theorem dvd_of_mem_productsAntidiagonal {n : ℕ} {f : ι → ℕ} (hf : f ∈ productsAntidiagonal n) (i : ι):
    f i ∣ n := by
  rw [←(mem_productsAntidiagonal.mp hf).1]
  apply Finset.dvd_prod_of_mem _ (mem_univ i)

theorem ne_zero_of_mem_productsAntidiagonal {n : ℕ} {f : ι → ℕ} (hf : f ∈ productsAntidiagonal n) (i : ι):
    f i ≠ 0 :=  
  ne_zero_of_dvd_ne_zero (mem_productsAntidiagonal.mp hf).2 (dvd_of_mem_productsAntidiagonal hf i)

theorem prod_eq_of_mem_productsAntidiagonal {n : ℕ} {f : ι → ℕ} (hf : f ∈ productsAntidiagonal n):
    ∏ i, f i = n :=  
  (mem_productsAntidiagonal.mp hf).1

theorem productsAntidiagonal_eq (d P: ℕ) (hdP : d ∣ P) (hP : P ≠ 0):
    productsAntidiagonal d = 
      (Fintype.piFinset fun _ : ι => P.divisors).filter fun s => ∏ i, s i = d := by
  ext _
  constructor
  · unfold productsAntidiagonal 
    simp_rw [mem_filter, Fintype.mem_piFinset]  
    intro ⟨h, hprod⟩
    simp_rw [mem_divisors] at h
    simp_rw [mem_divisors]
    refine ⟨ fun i => ⟨Trans.trans (h i).1 hdP, hP⟩, hprod⟩ 
  · rw [mem_productsAntidiagonal]
    simp_rw [mem_filter, Fintype.mem_piFinset] 
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_of_dvd_ne_zero hP hdP⟩ 

lemma image_apply_productsAntidiagonal [Nontrivial ι] {n : ℕ} {i : ι} :
    (productsAntidiagonal (ι:=ι) n).image (fun f => f i) = divisors n := by
  ext k
  simp only [mem_image, mem_productsAntidiagonal, ne_eq, mem_divisors, Nat.isUnit_iff]
  constructor
  · intro ⟨f, ⟨hf, hn⟩, hk⟩
    refine ⟨?_, hn⟩
    rw [←hf, ←hk]
    exact dvd_prod_of_mem f (mem_univ _)
  · rintro ⟨⟨r, rfl⟩, hn⟩
    obtain ⟨i', hi'⟩ := Decidable.exists_ne i
    use fun j => if j = i then k else if j = i' then r else 1
    simp only [ite_true, and_true, hn]
    rw [←Finset.mul_prod_erase (a:=i) (h:=mem_univ _),
      ←Finset.mul_prod_erase (a:= i')]
    · rw [if_neg hi', if_pos rfl, if_pos rfl, prod_eq_one]
      · ring
      intro j hj
      simp only [mem_univ, not_true, mem_erase, ne_eq, and_true, not_not] at hj 
      rw [if_neg hj.1, if_neg hj.2]
    rw [mem_erase]
    exact ⟨hi',mem_univ _⟩

lemma image_piFinTwoEquiv {n : ℕ} :
    (productsAntidiagonal n).image (piFinTwoEquiv $ fun _ => ℕ) = divisorsAntidiagonal n := by
  ext x
  simp only [piFinTwoEquiv_apply, mem_image, mem_productsAntidiagonal, Fin.prod_univ_two, ne_eq,
    mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    use fun i => if i = 0 then x.fst else x.snd
    simp only [ite_true, ite_false, Prod.mk.eta, and_true, h]

lemma filter_factors {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    n.factors.toFinset.filter fun p => p ∣ m = m.factors.toFinset := by 
  ext p
  simp_rw [mem_filter, List.mem_toFinset]
  rw [mem_factors hn, mem_factors (ne_zero_of_dvd_ne_zero hn hmn)]
  exact ⟨(by tauto), fun ⟨hp, hpm⟩ => ⟨⟨hp, Trans.trans hpm hmn⟩, hpm⟩⟩

lemma productsAntidiagonal_exists_unique_prime_dvd {n p : ℕ} (hn : Squarefree n) 
    (hp : p ∈ n.factors) (f : ι → ℕ) (hf : f ∈ productsAntidiagonal n) :
    ∃! i, p ∣ f i := by 
  rw [mem_productsAntidiagonal] at hf
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
    Nat.bij n f hf ∈ productsAntidiagonal n := by
  rw [mem_productsAntidiagonal]
  refine ⟨?_, hn.ne_zero⟩
  unfold Nat.bij
  rw [prod_fiberwise, prod_attach (f := fun x => x)]
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
    (t : ι → ℕ) (ht : t ∈ productsAntidiagonal n) : ∃ g hg, Nat.bij n g hg = t := by
  have exists_unique := fun (p : ℕ) (hp : p ∈ n.factors.toFinset) => 
    (productsAntidiagonal_exists_unique_prime_dvd hn (List.mem_toFinset.mp hp) t ht)
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
  · apply dvd_of_mem_productsAntidiagonal ht
  rw [filter_factors this hn.ne_zero]
  apply prod_factors_toFinset_of_squarefree $ hn.squarefree_of_dvd this

theorem card_productsAntidiagonal_pi (n : ℕ) (hn : Squarefree n) : 
    (n.factors.toFinset.pi (fun _ => (univ : Finset ι))).card = 
      (productsAntidiagonal (ι:=ι) n).card := 
  Finset.card_congr (bij n) (Nat.bij_img n hn) (Nat.bij_inj n hn) (Nat.bij_surj n hn)

theorem card_productsAntidiagonal {d : ℕ} (hd : Squarefree d) (k : ℕ) :
    (productsAntidiagonal (ι:=Fin k) d).card = k ^ ω d := by
  rw [←card_productsAntidiagonal_pi d hd, Finset.card_pi, Finset.prod_const, card_fin,
    cardDistinctFactors_apply, List.card_toFinset]
  
example (n : ℕ) : normalize n = n := by
  exact normalize_eq n

@[reducible]
private def f : ∀ (a : Fin 3 → ℕ) (_ : a ∈ productsAntidiagonal n), ℕ × ℕ := fun a _ =>
    (a 0 * a 1, a 0 * a 2) 

private theorem productsAntidiagonal_three : ∀ (a : Fin 3 → ℕ) (_ : a ∈ productsAntidiagonal n), a 0 * a 1 * a 2 = n := by
    intro a ha
    rw [← (mem_productsAntidiagonal.mp ha).1, Fin.prod_univ_three a]

private theorem f_img {n : ℕ} (hn : Squarefree n) : ∀ (a : Fin 3 → ℕ) (ha : a ∈ productsAntidiagonal n),
      f a ha ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) := by
  intro a ha
  rw [mem_filter, Finset.mem_product, mem_divisors, mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ←productsAntidiagonal_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left, Nat.Coprime.lcm_eq_mul]
  · ring
  refine coprime_of_squarefree_mul (hn.squarefree_of_dvd ?_)
  use a 0; rw [←productsAntidiagonal_three a ha]; ring

private theorem f_inj {n : ℕ} :
    ∀ (a b : Fin 3 → ℕ) (ha : a ∈ productsAntidiagonal n) (hb : b ∈ productsAntidiagonal n),
      f a ha = f b hb → a = b := by
  intro a b ha hb hfab
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab 
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2
  · rw [productsAntidiagonal_three a ha, hfab1, productsAntidiagonal_three b hb]
  have hab2 : a 2 = b 2
  · rw [← mul_right_inj' $ mul_ne_zero (ne_zero_of_mem_productsAntidiagonal ha 0) 
      (ne_zero_of_mem_productsAntidiagonal ha 1)]
    exact hprods
  have hab0 : a 0 = b 0
  · rw [hab2] at hfab2 
    exact (mul_left_inj' $ ne_zero_of_mem_productsAntidiagonal hb 2).mp hfab2;
  have hab1 : a 1 = b 1
  · rw [hab0] at hfab1 
    exact (mul_right_inj' $ ne_zero_of_mem_productsAntidiagonal hb 0).mp hfab1; 
  funext i; fin_cases i <;> assumption

private theorem f_surj {n : ℕ} (hn : n ≠ 0) : 
    ∀ b : ℕ × ℕ,
      b ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) →
        ∃ (a : Fin 3 → ℕ) (ha : a ∈ productsAntidiagonal n), f a ha = b := by
  intro b hb
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := fun i : Fin 3 => if i = 0 then g else if i = 1 then b.fst / g else b.snd / g
  have ha : a ∈ productsAntidiagonal n := by
    rw [mem_productsAntidiagonal]
    rw [mem_filter, Finset.mem_product] at hb 
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      simp_rw [ite_true, ite_false]
      rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _), ←hb.2, lcm, 
        Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
  use a; use ha
  apply Prod.ext <;> simp_rw [ite_true, ite_false] <;> apply Nat.mul_div_cancel'
  · apply Nat.gcd_dvd_left 
  · apply Nat.gcd_dvd_right

theorem card_lcm_eq {n : ℕ} (hn : Squarefree n) :
    Finset.card ((n.divisors ×ˢ n.divisors).filter fun ⟨x, y⟩ => x.lcm y = n) =
      3 ^ ω n := by
  rw [← card_productsAntidiagonal hn 3, eq_comm]
  apply Finset.card_congr f (f_img hn) (f_inj) (f_surj hn.ne_zero)

end Nat