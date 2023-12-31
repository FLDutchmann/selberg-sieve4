/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Analysis.Normed.Field.InfiniteSum

open BigOperators Finset

@[simps! apply symm_apply]
def finset_insert_equiv_set_insert {ι : Type _} [DecidableEq ι] {s : Finset ι} {j : ι}
    [DecidablePred fun x => x ∈ s] :
    (insert j s : Finset ι) ≃ (insert j s : Set ι) := Equiv.subtypeEquiv (Equiv.refl ι) (by simp)
    --Equiv.cast (by simp [Set.coe_eq_subtype])

set_option trace.simps.verbose true in
@[simps! apply symm_apply]
def finset_insert_equiv_PUnit {ι : Type _} [DecidableEq ι] {s : Finset ι} {j : ι} (hj : j ∉ s) [DecidablePred fun x => x ∈ s] :
    (insert j s : Finset ι) ≃ s ⊕ PUnit := finset_insert_equiv_set_insert.trans (Equiv.Set.insert hj)

universe u_1 u_2 u_3
#check Equiv.Set.insert
def insert_pi_equiv {ι : Type u_1} [DecidableEq ι] {α : Type u_2} (s : Finset ι) {j : ι} (hj : j ∉ s) :
  (((insert j s:Finset ι)) → α) ≃ ((s → α) × α) := calc
  (((insert j s:Finset ι)) → α) ≃ ((s ⊕ PUnit.{u_1+1}) → α) := Equiv.arrowCongr
                                (finset_insert_equiv_PUnit hj) (Equiv.refl _)
  _ ≃ ((s → α) × (PUnit.{u_1+1} → α)) := Equiv.sumArrowEquivProdArrow ..
  _ ≃ ((s → α) × α) := Equiv.prodCongrRight (fun _ => Equiv.punitArrowEquiv α)

-- @[simp]
-- theorem insert_pi_equiv_apply_fst {ι : Type u_1} [DecidableEq ι] (α : Type u_2)
--     (s : Finset ι) (j : ι) (hj : j ∉ s) (f : ((insert j s:Finset ι)) → α) :
--     (insert_pi_equiv s hj f) = ⟨fun (i:s) => f ⟨i, mem_insert_of_mem i.2⟩, f ⟨j, mem_insert_self ..⟩⟩ := by
--   ext i
--   · simp [insert_pi_equiv]
--     sorry
--   sorry
--

theorem insert_pi_equiv_symm_apply_self {ι : Type u_1} [DecidableEq ι] (α : Type u_2)
    (s : Finset ι) (j : ι) (hj : j ∉ s) (x : (s → α) × α) :
    (insert_pi_equiv (α := α) s hj).symm x ⟨j, mem_insert_self ..⟩ = x.2 := by
  classical
  simp only [insert_pi_equiv, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.symm_trans_apply,
    Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Equiv.symm_symm,
    Function.comp_apply, finset_insert_equiv_PUnit_apply, id_eq]
  erw [Equiv.Set.insert_apply_left (a:=j) hj, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  unfold Equiv.punitArrowEquiv
  simp

theorem insert_pi_equiv_symm_apply_of_mem {ι : Type u_1} [DecidableEq ι] (α : Type u_2)
    (s : Finset ι) (j : ι) (hj : j ∉ s) (x : (s → α) × α) (i : s) :
    (insert_pi_equiv (α := α) s hj).symm x ⟨i, mem_insert_of_mem i.2⟩ =
      x.1 i:= by
  classical
  simp [insert_pi_equiv]
  erw [Equiv.Set.insert_apply_right (a:=j) hj]
  erw [Equiv.sumArrowEquivProdArrow_symm_apply_inl]

theorem prod_summable_norm_of_summable_norm {R : Type _} {ι : Type _} {α : Type _} {s : Finset ι}
  [DecidableEq ι] [inst : NormedCommRing R] {f : (i:ι) → α → R} (hf : ∀ i ∈ s, Summable fun x => ‖f i x‖) :
    Summable fun (x : (i:s) → α) => ‖∏ i in s.attach, f i (x i)‖  := by
  induction s using Finset.induction with
  | empty => exact summable_of_finite_support (Set.toFinite _)
  | @insert a s has ih =>
    rw [Finset.attach_insert]
    conv =>
      congr; ext x
      rw [Finset.prod_insert (by simp[has]), mul_comm]
    rw [←Equiv.summable_iff (insert_pi_equiv (hj := has) ..).symm]
    simp only [Function.comp, insert_pi_equiv_symm_apply_of_mem (hj:=has),
      insert_pi_equiv_symm_apply_self (hj:=has), mem_attach, Subtype.mk.injEq, forall_true_left,
      Subtype.forall, imp_self, implies_true, prod_image, Subtype.coe_eta, dite_eq_ite, dite_true]
    apply Summable.mul_norm (ι:=s→α) (ih fun i hi => hf i (mem_insert_of_mem hi)) (hf a (Finset.mem_insert_self ..))

theorem prod_tsum_of_summable_norm {R : Type u_1} {ι : Type u_2} {α : Type u_3}  {s : Finset ι} [inst : NormedCommRing R]
    [DecidableEq ι] [inst : CompleteSpace R] {f : ι → α → R} (hf : ∀ i ∈ s, Summable fun x => ‖f i x‖) :
    ∏ i in s, ∑' (x:α), f i x = ∑' (a : (i:s) → α), ∏ i in s.attach, f i (a i)  := by
  induction s using Finset.induction with
  | empty =>
    simp (config := { decide := true }) only [prod_empty, attach_empty, tsum_const, not_mem_empty,
      Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton, one_smul]
  | @insert j s hjs ih =>
    rw [Finset.prod_insert hjs, ih,mul_comm, tsum_mul_tsum_of_summable_norm]
    rw [←Equiv.tsum_eq (insert_pi_equiv (s:=s) hjs).symm]
    · congr
      ext a
      rw [Finset.attach_insert, Finset.prod_insert, mul_comm];
      simp only [insert_pi_equiv_symm_apply_self (hj := hjs), mem_attach, Subtype.mk.injEq, forall_true_left,
        Subtype.forall, imp_self, implies_true, prod_image, insert_pi_equiv_symm_apply_of_mem (hj := hjs)]
      rw [mem_image]; push_neg
      simp only [mem_attach, ne_eq, Subtype.mk.injEq, forall_true_left, Subtype.forall]
      rintro i hi rfl
      exact hjs hi
    · exact prod_summable_norm_of_summable_norm fun i hi => hf i (mem_insert_of_mem hi)
    · exact hf j (mem_insert_self j s)
    · exact fun i hi => hf i (mem_insert_of_mem hi)

#exit
-- consider Equiv.piCurry
#check Insert.rec
def Equiv.sumPiEquivProdPi (α β : Type _) (γ : (α ⊕ β → Type _)):
    ((i : α ⊕ β) → γ i) ≃ ((i : α) → γ (Sum.inl i)) × ((i : β) → γ (Sum.inr i)) := ⟨
  fun f => ⟨ fun a => (f (Sum.inl a)), fun b => f (Sum.inr b)⟩,
  fun p => Sum.rec (p.1) (p.2),
  fun f => by ext i; cases i with | _ => simp,
  fun _ => by simp⟩

def test (a b : Type _) (h : a = b) : a ≃ b :=  Equiv.cast h

def tmp0  {ι : Type _} [DecidableEq ι] {s : Finset ι} {j : ι} (hj : j ∉ s) [DecidablePred fun x => x ∈ s] :
    (insert j s:Set ι) ≃ (s) ⊕ PUnit := Equiv.Set.insert hj

def tmp1 {ι : Type _} [DecidableEq ι] {s : Finset ι} {j : ι} [DecidablePred fun x => x ∈ s] :
    (insert j s:Finset ι) ≃ (insert j s :Set ι) := Equiv.cast (by simp [Set.coe_eq_subtype])

def tmp2  {ι : Type _} [DecidableEq ι] {s : Finset ι} {j : ι} (hj : j ∉ s) [DecidablePred fun x => x ∈ s] :
    (insert j s:Finset ι) ≃ s ⊕ PUnit := Trans.trans (tmp1)  (tmp0 hj)

#check fun j s (h : j ∉ s) => (calc _ ≃ _ := (tmp1)
                                    _ ≃ _ := (tmp0 h))

def cast' {α β : Sort _} (h : α = β) : α ≃ β :=
  ⟨cast h, cast h.symm, fun _ => by cases h; rfl, fun _ => by cases h; rfl⟩

#check Subtype.rec

example {α: Type _} {P Q : α → Prop} (h : {x // P x} = {x // Q x}) (a : {x // P x}) :
    (cast h a).val = a.val := by

  rw [←Subtype.heq_iff_coe_eq]
  apply cast_heq h
  apply_fun Subtype.rec (fun _ p => p) at h

#exit
  intro x
  have : (Subtype P).2 = (Subtype Q).2
  · sorry
  constructor
  . intro hQ
    let y : {x // P x} := h.symm ▸ ⟨x, hQ⟩
    have : x = y.val
    · dsimp only; rfl
/-
def tmp  {ι : Type _} [DecidableEq ι] (α : ι → Type _) (s : Finset ι) [DecidablePred fun x => x ∈ s] (j : ι) (hj : j ∉ s) :
    ((i : (insert j s:Finset ι)) → α i) ≃ ((i : s) → α i) × α j :=
    Equiv.trans (Equiv.piCongrLeft _ (tmp2 hj)) _ -/
-- (i : (s ⊕ punit) → α i)
def insert_pi_equiv {ι : Type _} [DecidableEq ι] (α : ι → Type _) (s : Finset ι) (j : ι) (hj : j ∉ s) :
  ((i : (insert j s:Finset ι)) → α i) ≃ (((i : s) → α i) × α j) :=
 calc ((i : (insert j s:Finset ι)) → α i)
        ≃ ((b : s ⊕ PUnit) → α ((tmp2 hj).symm b)) := Equiv.piCongrLeft' _ (tmp2 hj)
      _ ≃ ((i : { x // x ∈ s }) → α ↑((tmp2 hj).symm (Sum.inl i))) × ((i : PUnit) → α ↑((tmp2 hj).symm (Sum.inr i))) := Equiv.sumPiEquivProdPi _ _ _
      _ ≃ ((i : { x // x ∈ s }) → α i) × ((i : PUnit) → α ↑((tmp2 hj).symm (Sum.inr i)))
      := Equiv.prodCongrLeft fun a => Equiv.piCongrRight (fun b => Equiv.cast (by
      apply congrArg;
      unfold tmp2; unfold tmp1; unfold tmp0;
      simp
      rw [Equiv.cast_eq_iff_heq]

      ))
      _ ≃ _ := sorry


 #exit
 ⟨
  fun p => fun i => if h : i = j then h.symm ▸ p.1 else p.2 ⟨i.1,or_iff_not_imp_left.mp (Finset.mem_insert.mp i.2) h⟩,
  fun x => ⟨x ⟨j, by rw [Finset.mem_insert]; left; rfl ⟩, fun i => x ⟨i, by rw [Finset.mem_insert]; right; exact i.2⟩ ⟩,
  by
    intro x; simp; ext i;
    · simp
    · simp; erw [dif_neg]; intro h; rw [← h] at hj; exact hj i.2  ,
  by
    intro x; simp; ext i
    by_cases h : i = j
    · rw [dif_pos h]
      rw [h.symm]
      sorry
    · rw [dif_neg h]
  ⟩

example (s : Set α) (hs : IsEmpty s) :  s.Finite := by exact Set.toFinite s

theorem prod_summable_norm_of_summable_norm {R : Type u_1} {ι : Type u_2} {α : ι → Type u_3} {s : Finset ι}
  [DecidableEq ι] [inst : NormedCommRing R] [inst : CompleteSpace R] {f : (i:ι) → α i → R} (hf : ∀ i ∈ s, Summable fun x => ‖f i x‖) :
    Summable fun (x : (i:s) → α i) => ‖∏ i in s.attach, f i (x i)‖  := by
  induction s using Finset.induction with
  | empty => exact summable_of_finite_support (Set.toFinite _)
  | @insert a s has ih =>
    rw [Finset.attach_insert]
    conv =>
      congr; ext x
      rw [Finset.prod_insert sorry]
    rw [←Equiv.summable_iff (insert_pi_equiv (hj := has) ..)]
    unfold Function.comp
    --apply Summable.mul_norm
    sorry

    --· rw [← Finset.prod_erase_mul (a := j) (f := fun i => f i (x i)) (h := j.2)]

  --apply Summable.mul_norm (hg := hf j) (g := fun x => f j (x))
-- ∏ p in n.factors.toFinset, f p
  sorry

/--/  · let x := Classical.choice hs
    exfalso; exact Finset.not_mem_empty x.1 x.2
  by_cases s.card = 1
  · sorry -/

theorem prod_tsum_of_summable_norm {R : Type u_1} {ι : Type u_2} {α : ι → Type u_3}  {s : Finset ι} [inst : NormedCommRing R]
  [inst : CompleteSpace R] {f : (i:ι) → α i → R} (hf : ∀ i, Summable fun x => ‖f i x‖) :
    ∏ i in s, ∑' (x:α i), f i x = ∑' (a : (i:ι) → α i), ∏ i in s, f i (a i)  := sorry
