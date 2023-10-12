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
import SelbergSieve.AesopDiv
import SelbergSieve.ForMathlib
import SelbergSieve.ForArithmeticFunction
import SelbergSieve.ForMathlib.ProdsAntidiagonal
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

noncomputable section

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)
open scoped BigOperators Nat.ArithmeticFunction

open Nat Nat.ArithmeticFunction Finset Tactic.Interactive

namespace Aux

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

theorem prod_le_prod_of_nonempty {t : Finset ℕ} (f g : ℕ → ℝ) (hf : ∀ n : ℕ, n ∈ t → 0 < f n)
    (hfg : ∀ n : ℕ, n ∈ t → f n < g n) (h_ne : t.Nonempty) : ∏ p in t, f p < ∏ p in t, g p :=
  by
  have hg : ∀ n : ℕ, n ∈ t → 0 < g n := by intro n hn; exact lt_trans (hf n hn) (hfg n hn)
  --revert h_ne hf hg hfg
  induction' t using Finset.induction_on with q s hqs h_ind
  simp at h_ne
  --intro q s hqs h_ind _ _ _ _
  have hq_in : q ∈ insert q s := by 
    rw [Finset.mem_insert]; exact Or.intro_left (q ∈ s) (rfl : q = q)
  rw [prod_insert hqs]
  rw [prod_insert hqs]
  apply mul_lt_mul
  exact hfg q hq_in
  by_cases hs_ne : s.Nonempty
  · apply le_of_lt
    apply h_ind _ _ hs_ne
    · intro n hn; apply hg; rw [mem_insert]; exact .inr hn
    · intro n hn; apply hf; rw [mem_insert]; exact .inr hn
    · intro n hn; apply hfg; rw [mem_insert]; exact .inr hn
  · suffices : s = ∅; rw [this]; simp only [le_refl, Finset.prod_empty]
    rw [not_nonempty_iff_eq_empty] at hs_ne ; exact hs_ne
  apply prod_pos; intro p hps; apply hf p; rw [mem_insert]; exact Or.intro_right (p = q) hps
  apply le_of_lt; exact hg q hq_in

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f) (l d : ℕ) (hdl : d ∣ l)
    (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) :=
  by
  apply div_eq_of_eq_mul hd
  have : l / d * d = l := by apply Nat.div_mul_cancel hdl
  rw [← h_mult.right]
  rw [this]
  apply coprime_of_squarefree_mul
  rw [this]; exact hl


theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 :=
  by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hl]
  rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]

theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 :=
  by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hl]
  rw [abs_pow]; simp
  
theorem prime_dvd_prod {α : Type _} {p : ℕ} (hp : p.Prime) {s : Finset α} (f : α → ℕ)
    (h_prod : p ∣ ∏ i in s, f i) : ∃ i, p ∣ f i :=
  by
  rcases (Prime.dvd_finset_prod_iff (Nat.Prime.prime hp) _).mp h_prod with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

theorem nat_sq_mono {a b : ℕ} (h : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  pow_mono_right 2 h

theorem inv_antitoneOn_pos : 
    AntitoneOn (fun x:ℝ ↦ x⁻¹) (Set.Ioi 0) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  refine (inv_le_inv hb ha).mpr (le_of_lt hab)

theorem inv_antitoneOn_Icc (a b : ℝ) (ha : 0 < a) : 
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b 
  · exact inv_antitoneOn_pos.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

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

theorem log_le_sum_one_div (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d in Finset.Icc 1 (⌊y⌋₊), 1 / (d:ℝ) := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast 
    exact ceil_le_floor_add_one y
  · simp_rw[one_div]
    apply log_add_one_le_sum_inv

example : 
   ∫ x in (0)..1, x = 1/2 := by
  rw [@integral_id]
  ring

theorem sum_one_div_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d in Finset.Icc 1 n, 1 / (d : ℝ) ≤ 1 + Real.log ↑n :=
  by
  suffices ∑ d : ℕ in Ioc 1 n, 1 / (d : ℝ) ≤ Real.log ↑n
    by
    calc
      _ = 1 + ∑ d : ℕ in Icc 2 n, 1 / (d : ℝ) := ?_
      _ ≤ 1 + Real.log ↑n := ?_
    { rw [← Finset.sum_erase_add (Icc 1 n) _ (_ : 1 ∈ Icc 1 n), Finset.Icc_erase_left, add_comm, cast_one, one_div_one]
      rfl; rw [Finset.mem_Icc]; exact ⟨le_rfl, hn⟩ }
    { apply _root_.add_le_add; exact le_rfl; exact this }
  calc
    ∑ d : ℕ in Ico 2 (n + 1), 1 / (d : ℝ) = ∑ d in Ico 2 (n + 1), 1 / (↑(d + 1) - 1) := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), 1 / (x - 1) := ?_
    _ = Real.log ↑n := ?_
  { apply sum_congr rfl ; intro d _ ; rw [(by norm_num : ↑(d + 1) - 1 = (d : ℝ))] }
  { apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => 1 / (x - 1) 
    apply succ_le_succ ; exact hn 
    dsimp only [AntitoneOn] 
    intro a ha b hb hab 
    have : ∀ x : ℝ, x ∈ Set.Icc (↑2 : ℝ) ↑(n + 1) → 0 < x - 1 := 
      by rintro x ⟨hx_1, _⟩; linarith 
    rw [_root_.one_div_le_one_div (this b hb) (this a ha)]; linarith }
  have two_sub_one : 2 - 1 = (1 : ℝ) := by norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, cast_add, cast_one]

  rw [add_sub_assoc, sub_self (1 : ℝ), add_zero, two_sub_one, integral_one_div, div_one]
  by_contra h; rw [Set.mem_uIcc] at h 
  cases' h with h h
  linarith only [h.1]
  rw [← cast_zero, cast_le] at h 
  linarith only [hn, h.1]


lemma _helper' {h P : ℕ} (a : Fin h → ℕ) (ha : a ∈ Fintype.piFinset fun _ => divisors P) (i:Fin h) : 
    0 < 1/(a i:ℝ) := by
  norm_num
  exact pos_of_mem_divisors (Fintype.mem_piFinset.mp ha i)


#check fun n : ℕ => ∫ x in (2 : ℝ)..(n + 1 : ℝ), 1 / (x - 1)
-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
  (hP : Squarefree P) :
    (∑ d in P.divisors, if ↑d ≤ x then (h:ℝ) ^ (ω d:ℕ) / (d : ℝ) else (0 : ℝ)) ≤ (1 + Real.log x) ^ h :=
  by
  have hx_pos : 0 < x
  · linarith
  calc
    _ = ∑ d in P.divisors, ite (↑d ≤ x) (↑(Nat.piMulAntidiagonal univ d: Finset ((Fin h) → ℕ)).card / (d : ℝ)) 0 := ?_
    _ = ∑ d in P.divisors, ↑(Nat.piMulAntidiagonal univ d : Finset ((Fin h) → ℕ)).card * ite (↑d ≤ x) (1 / (d : ℝ)) 0 := ?_
    _ =
        ∑ d in P.divisors,
          ∑ a in Fintype.piFinset fun _i : Fin h => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then 1 / (d : ℝ) else 0 else 0 := ?_
    _ =
        ∑ a in Fintype.piFinset fun _i : Fin h => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, 1 / (a i : ℝ) else 0 else 0 := ?_
    _ ≤
        ∑ a in Fintype.piFinset fun _i : Fin h => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, 1 / (a i : ℝ) else 0 := ?_ -- do we need this one?
    _ ≤
        ∑ a in Fintype.piFinset fun _i : Fin h => P.divisors,
          ∏ i, if ↑(a i) ≤ x then 1 / (a i : ℝ) else 0 := ?_
    _ = ∏ i : Fin h, ∑ d in P.divisors, if ↑d ≤ x then 1 / (d : ℝ) else 0 := ?_
    _ = (∑ d in P.divisors, if ↑d ≤ x then 1 / (d : ℝ) else 0) ^ h := ?_
    _ ≤ (1 + Real.log x) ^ h := ?_
  · apply sum_congr rfl; intro d hd; apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
    intro; norm_cast; rw [← card_piMulAntidiagonal_fin (hP.squarefree_of_dvd (mem_divisors.mp hd).1) h]
  · apply sum_congr rfl; intro d _; rw [← ite_mul_zero_right]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
    intro _; rw [mul_one_div]
  · apply sum_congr rfl; intro d hd
    rw [Finset.card_eq_sum_ones, cast_sum, cast_one, sum_mul, one_mul]
    simp_rw [(piMulAntidiagonal_univ_eq _ _ (dvd_of_mem_divisors hd)) hP.ne_zero]
    rw [sum_filter]; apply sum_congr rfl; 
    intro a _
    have : ∏ i, a i = d ↔ ∏ i, a i = d ∧ d ∣ P := 
      by rw [mem_divisors] at hd ; rw [iff_self_and]; exact fun _ => hd.1
    rw [if_ctx_congr this (fun _ => rfl) (fun _ => rfl)]
  · rw [sum_comm]; apply sum_congr rfl; intro a ha; rw [sum_eq_single (∏ i, a i)]
    apply if_ctx_congr _ _ (fun _ => rfl); rw [Iff.comm, iff_and_self]; exact fun _ => rfl
    intro; rw [one_div, cast_prod, ← prod_inv_distrib, if_ctx_congr Iff.rfl _ (fun _ => rfl)]
    intro; apply prod_congr rfl; intro _ _; rw [one_div]
    intro d _ hd_ne; rw [ne_comm] at hd_ne ; rw [if_neg]; by_contra h; exact hd_ne h.1
    intro h; rw [if_neg]; aesop_div
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    by_cases h' : (∏ i, a i ≤ x)
    swap; rw[if_neg h']
    rw [if_pos h']; apply prod_nonneg; intro i _; 
    apply one_div_nonneg.mpr; norm_num
  · apply sum_le_sum; intro a ha
    by_cases h : (∏ i, a i ≤ x)
    · rw [if_pos h]
      apply prod_le_prod; intro i _
      apply one_div_nonneg.mpr; norm_num
      intro i hi
      rw [if_pos]
      trans (∏ j, (a j:ℝ))
      · norm_cast
        rw [←prod_erase_mul (a:=i) (h:= hi)]
        apply Nat.le_mul_of_pos_left
        rw [Fintype.mem_piFinset] at ha
        apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
      rw [←cast_prod]; exact h
    · rw [if_neg h]
      apply prod_nonneg; intro j _
      by_cases h' : ↑(a j) ≤ x
      swap; rw [if_neg h']
      rw [if_pos h']
      exact le_of_lt $ _helper' a ha j
  · rw [prod_univ_sum]
  save
  · rw [prod_const, card_fin]
  · apply pow_le_pow_of_le_left (b:= 1 + Real.log x)
    · apply sum_nonneg; intro d _
      by_cases h': ↑d ≤ x
      · rw [if_pos h', one_div_nonneg]; norm_num
      · rw [if_neg h']
    trans (∑ d in Icc 1 (floor x), 1/↑d)
    · rw [←sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      intro d; rw[mem_filter, mem_Icc]
      intro hd
      constructor
      · rw [Nat.succ_le]; exact pos_of_mem_divisors hd.1
      · rw [le_floor_iff]; exact hd.2; 
        apply le_of_lt; exact hx_pos
      intro k _ _
      rw [one_div_nonneg]; norm_num 
    trans (1 + Real.log (floor x))
    apply sum_one_div_le_log
    apply le_floor; rw[cast_one]; exact hx
    apply _root_.add_le_add le_rfl
    rw [Real.log_le_log]; apply floor_le
    exact le_of_lt hx_pos
    norm_cast; rw [←Nat.succ_le]; apply le_floor; rw [cast_one]; exact hx
    exact hx_pos
    

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d in P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤ x * (1 + Real.log x) ^ h := by
  trans (∑ d in P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · apply sum_le_sum; intro d hd
    rw [←ite_mul_zero_right]
    by_cases hdx : (d:ℝ) ≤ x
    swap; rw[if_neg hdx, if_neg hdx]
    rw [if_pos hdx, if_pos hdx]
    trans (x/d * (h:ℝ)^ω d)
    · apply le_mul_of_one_le_left
      apply pow_nonneg; norm_num
      rw [one_le_div]; exact hdx
      norm_cast; exact pos_of_mem_divisors hd
    · apply le_of_eq; ring
  rw [←mul_sum]; apply mul_le_mul le_rfl
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP
  apply sum_nonneg; intro d _
  by_cases h' : ↑d ≤ x
  swap; rw [if_neg h']
  rw[if_pos h']
  apply div_nonneg; norm_num; norm_num
  linarith  

end Aux

