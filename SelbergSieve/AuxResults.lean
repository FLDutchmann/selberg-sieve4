/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.List.Func
--import SelbergSieve.AesopDiv
import SelbergSieve.ForMathlib
import SelbergSieve.ForArithmeticFunction
import SelbergSieve.ForMathlib.ProdsAntidiagonal
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Data.Nat.Prime

noncomputable section

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)
open scoped BigOperators Nat.ArithmeticFunction

open Nat Nat.ArithmeticFunction Finset Tactic.Interactive

namespace Aux


example (n: ℕ) (X : ℝ) : n * X * n = X * (n^2) := by
  push_cast
  ring


theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d in n.divisors, f d = ∑ d in P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]
    
theorem sum_intro {α M: Type _} [AddCommMonoid M] [DecidableEq α] (s : Finset α) {f : α → M} (d : α)
     (hd : d ∈ s) :
    f d = ∑ k in s, if k = d then f k else 0 := by
  trans (∑ k in s, if k = d then f d else 0)
  · rw [sum_eq_single_of_mem d hd]
    rw [if_pos rfl]
    intro _ _ h; rw [if_neg h]
  apply sum_congr rfl; intro k _; apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
  intro h; rw [h]

lemma neq_lcm_of_ndvd' {d1 d2 d n : ℕ} (hn : d ∈ divisors n) : (¬d1 ∈ divisors d) → ¬d = d1.lcm d2 := by
  contrapose!
  rw [mem_divisors]
  rintro rfl
  refine ⟨Nat.dvd_lcm_left _ _, Nat.ne_of_gt (pos_of_mem_divisors hn)⟩

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x in s, f x) else 0) = ∑ x in s, if p then f x else 0 := by 
  by_cases hp : p
  · simp_rw [if_pos hp]
  · simp_rw [if_neg hp, sum_const_zero]
  
theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d in n.divisors,
        ∑ d1 in d.divisors,
          ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d in n.divisors,
        ∑ d1 in n.divisors,
          ∑ d2 in n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 :=
  by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero, ←ite_and]
  apply sum_congr rfl; intro d1 _
  apply sum_congr rfl; intro d2 _
  congr
  rw [eq_iff_iff]
  constructor
  · intro ⟨_,_,h⟩; exact h
  · intro h; rw[h]; exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩ 
  
theorem dvd_iff_mul_of_dvds {P : ℕ} (k d l m : ℕ) (hd : d ∈ P.divisors) :
    k = d / l ∧ l ∣ d ∧ d ∣ m ↔ d = k * l ∧ d ∣ m :=
  by
  constructor
  · intro ⟨hk_eq, hld, hdm⟩
    exact ⟨Nat.eq_mul_of_div_eq_left hld hk_eq.symm, hdm⟩
  · intro ⟨hd_eq, hdm⟩
    refine ⟨?_, ?_, hdm⟩
    · apply (Nat.div_eq_of_eq_mul_left _ hd_eq).symm
      apply Nat.pos_of_ne_zero
      apply right_ne_zero_of_mul (a:=k)
      rw [←hd_eq]
      apply _root_.ne_of_gt
      apply Nat.pos_of_mem_divisors hd
    · use k; rw [hd_eq, mul_comm]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d in m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero $ Squarefree.ne_zero hm
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on Squarefree (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]-- 
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←Nat.ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime, 
        hmul]
      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw[if_neg $ hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd) 
  

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d in P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  have hP_ne_zero : P ≠ 0 := Squarefree.ne_zero hP
  have hm_ne_zero : m ≠ 0 := ne_zero_of_dvd_ne_zero hP_ne_zero hm
  have hsub: m.divisors ⊆ P.divisors := Nat.divisors_subset_of_dvd hP_ne_zero hm
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP), ←sum_subset hsub]
  · apply sum_congr rfl; intro d hd; apply if_congr _ rfl rfl
    exact and_iff_left (dvd_of_mem_divisors hd)
  · intro d _ hdm; rw [if_neg]
    by_contra h; rw [mem_divisors] at hdm; 
    exact hdm ⟨h.2, hm_ne_zero⟩ 

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d in P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) = if l = m then (μ l : ℝ) else 0 :=
  by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem gcd_dvd_mul (m n : ℕ) : m.gcd n ∣ m * n := by
  calc
    m.gcd n ∣ m := Nat.gcd_dvd_left m n
    _ ∣ m * n := ⟨n, rfl⟩

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f) {m n : ℕ}
    (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 :=
  by
  cases' hmn with k hk
  rw [hk]
  rw [hk] at h_sq 
  have : m.Coprime k := coprime_of_squarefree_mul h_sq
  rw [IsMultiplicative.map_mul_of_coprime h_mult this]
  rw [h_zero]; simp only [MulZeroClass.zero_mul, eq_self_iff_true]

example (t : Finset ℕ) : t.val.prod = ∏ i in t, i :=
  prod_val t

set_option profiler true

#check prod_lt_prod'
#check prod_le_prod

theorem prod_lt_prod  {R : Type*} [StrictOrderedCommSemiring R] {t : Finset ℕ} {f g : ℕ → R} (hf : ∀ n ∈ t, 0 < f n)
    (hfg : ∀ n ∈ t, f n ≤ g n) (hlt : ∃ n ∈ t, f n < g n) : ∏ p in t, f p < ∏ p in t, g p := by 
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi, prod_insert (not_mem_erase _ _), prod_insert (not_mem_erase _ _)]
  apply mul_lt_mul hilt
  · exact prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj))) (fun _ hj ↦ hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact le_of_lt <| (hf i hi).trans hilt

theorem prod_le_prod_of_nonempty {R : Type*} [StrictOrderedCommSemiring R] {t : Finset ℕ} (f g : ℕ → R) (hf : ∀ n : ℕ, n ∈ t → 0 < f n)
    (hfg : ∀ n : ℕ, n ∈ t → f n < g n) (h_ne : t.Nonempty) : ∏ p in t, f p < ∏ p in t, g p := by
  apply prod_lt_prod hf fun n hn => le_of_lt (hfg n hn)
  obtain ⟨n, hn⟩ := h_ne
  exact ⟨n, hn, hfg n hn⟩

theorem primeDivisors_nonempty (n : ℕ) (hn : 2 ≤ n) : n.factors.toFinset.Nonempty := by
  unfold Finset.Nonempty
  simp_rw[List.mem_toFinset, Nat.mem_factors (show n ≠ 0 by linarith)]
  apply Nat.exists_prime_and_dvd; linarith

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f) (l d : ℕ) (hdl : d ∣ l)
    (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) :=
  by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl] 
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl


theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hl, ←pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 := by
  simp only [ArithmeticFunction.moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]
  
theorem nat_sq_mono {a b : ℕ} (h : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  pow_mono_right 2 h

theorem inv_sub_antitoneOn_gt {R : Type*} [LinearOrderedField R] (c : R) : 
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr; linarith

theorem inv_sub_antitoneOn_Icc {R : Type*} [LinearOrderedField R]  (a b c: R) (ha : c < a) : 
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b 
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos {R : Type*} [LinearOrderedField R] : 
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem inv_antitoneOn_Icc {R : Type*} [LinearOrderedField R] (a b : R) (ha : 0 < a) : 
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem log_add_one_le_sum_inv (n : ℕ) : 
    Real.log ↑(n+1) ≤ ∑ d in Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d in Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast 
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv


example : 
   ∫ x in (0)..1, x = 1/2 := by
  rw [@integral_id]
  ring

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d in Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [gt_iff_lt, lt_one_iff, mem_Icc, true_and, not_le, Icc_erase_left]
  calc
    ∑ d : ℕ in Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d in Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹ 
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d in Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

theorem Nat.le_prod [DecidableEq ι] {f : ι → ℕ} {s : Finset ι} {i : ι} (hi : i ∈ s) (hf : ∀ i ∈ s, f i ≠ 0):
    f i ≤ ∏ j in s, f j := by
  rw [←prod_erase_mul (a:=i) (h:= hi)]
  exact le_mul_of_pos_left (prod_pos fun j hj => Nat.pos_of_ne_zero (hf j (mem_of_mem_erase hj)))


-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
  (hP : Squarefree P) :
    (∑ d in P.divisors, if d ≤ x then (k:ℝ) ^ (ω d:ℕ) / (d : ℝ) else (0 : ℝ)) ≤ (1 + Real.log x) ^ k :=
  by
  have hx_pos : 0 < x
  · linarith
  calc
    _ = ∑ d in P.divisors,
          ∑ a in Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ =
        ∑ a in Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤
        ∑ a in Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_ -- do we need this one?
    _ ≤  
        ∑ a in Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d in P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d in P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by rw [prod_const, card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_
  
  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd 
    simp_rw [ite_and]; 
    rw [←sum_filter, Finset.sum_const, ←piMulAntidiagonal_univ_eq _ _ hd.1 hd.2, card_piMulAntidiagonal_fin 
      <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, one_mul, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl); rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h' 
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h 
    · gcongr with i hi
      · norm_num
      rw [if_pos] 
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  save
  · rw [←sum_filter]
    gcongr
    · apply sum_nonneg; intro _ _
      norm_num
    trans (∑ d in Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      intro d; rw[mem_filter, mem_Icc]
      intro hd
      constructor
      · rw [Nat.succ_le]; exact pos_of_mem_divisors hd.1
      · rw [le_floor_iff]; exact hd.2; 
        apply le_of_lt; exact hx_pos
      norm_num 
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d in P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤ x * (1 + Real.log x) ^ h := by
  trans (∑ d in P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum]; 
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP


end Aux

