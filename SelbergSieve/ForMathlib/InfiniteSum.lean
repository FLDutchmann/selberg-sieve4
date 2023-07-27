/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Analysis.Normed.Field.InfiniteSum

open BigOperators 

open Finset


theorem prod_summable_norm_of_summable_norm {R : Type u_1} {ι : Type u_2} {α : ι → Type u_3} {s : Finset ι} [inst : NormedCommRing R] [inst : CompleteSpace R] 
  {f : (i:ι) → α i → R} (hf : ∀ i, Summable fun x => ‖f i x‖) :
    Summable fun (x : (i:ι) → α i) => ‖∏ i in s, f i (x i)‖  := sorry 
 

theorem prod_tsum_of_summable_norm {R : Type u_1} {ι : Type u_2} {α : ι → Type u_3}  {s : Finset ι} [inst : NormedCommRing R] [inst : CompleteSpace R] 
  {f : (i:ι) → α i → R} (hf : ∀ i, Summable fun x => ‖f i x‖) :
    ∏ i in s, ∑' (x:α i), f i x = ∑' (a : (i:ι) → α i), ∏ i in s, f i (a i)  := sorry 