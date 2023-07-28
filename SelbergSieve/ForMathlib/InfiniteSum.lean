/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Data.Finset.Basic

open BigOperators Finset

def insert_pi_equiv {ι : Type _} [DecidableEq ι] (α : ι → Type _) (s : Finset ι) (j : ι) (hj : j ∉ s) :
  ((i : (insert j s:Finset ι)) → α i) ≃ (α j × ((i : s) → α i)) := sorry

theorem prod_summable_norm_of_summable_norm {R : Type u_1} {ι : Type u_2} {α : ι → Type u_3} {s : Finset ι} (hs : Nonempty s) 
  [DecidableEq ι] [inst : NormedCommRing R] [inst : CompleteSpace R] {f : (i:ι) → α i → R} (hf : ∀ i ∈ s, Summable fun x => ‖f i x‖) :
    Summable fun (x : (i:s) → α i) => ‖∏ i in s.attach, f i (x i)‖  := by 
  induction s using Finset.strongInduction with | H s ih => 
  let j := Classical.choice hs
  conv => 
    congr
    ext x
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