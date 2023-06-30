/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Squarefree
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.List.Func
import SelbergSieve.Tmp
import SelbergSieve.AesopDiv

noncomputable section

open scoped BigOperators Classical Nat.ArithmeticFunction

open Nat Nat.ArithmeticFunction Finset Tactic.Interactive

namespace Aux

def Multiplicative (f : ℕ → ℝ) : Prop :=
  f 1 = 1 ∧ ∀ x y : ℕ, x.coprime y → f (x * y) = f x * f y

-- Rephrasing sum_subset_zero_on_sdiff for our context
theorem sum_over_dvd {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P) {f g : ℕ → α}
    (hf : ∀ d : ℕ, d ∣ P ∧ ¬d ∣ n → f d = 0) (hfg : ∀ d : ℕ, d ∣ n → f d = g d) :
    ∑ d in n.divisors, g d = ∑ d in P.divisors, f d :=
  by
  apply sum_subset_zero_on_sdiff
  · exact Nat.divisors_subset_of_dvd hP hn
  · intro d hd
    rw [mem_sdiff] at hd
    apply hf
    aesop_div
  · intro d hd
    rw [eq_comm]
    apply hfg d
    exact dvd_of_mem_divisors hd

theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d in n.divisors, f d = ∑ d in P.divisors, if d ∣ n then f d else 0 :=
  by
  apply sum_subset_zero_on_sdiff
  · exact Nat.divisors_subset_of_dvd hP hn
  · intro d hd
    apply if_neg
    rw [Finset.mem_sdiff] at hd; 
    aesop_div
  · intro d hd
    rw [if_pos (dvd_of_mem_divisors hd)]
    

theorem sum_intro {α : Type _} [Ring α] (s : Finset ℕ) (p : Prop) [Decidable p] (x : α) (d : ℕ)
    [∀ k : ℕ, Decidable (k = d ∧ p)] (hd : p → d ∈ s) :
    (if p then x else 0) = ∑ k in s, if k = d ∧ p then x else 0 :=
  by
  by_cases hp : p
  · rw [if_pos hp]
    rw [sum_eq_single_of_mem d (hd hp)]
    rw [if_pos (⟨rfl, hp⟩ : d = d ∧ p)]
    intro b hbs hbd
    have : ¬(b = d ∧ p)
    push_neg; contrapose!; intro; exact hbd
    rw [if_neg this]
  · rw [if_neg hp]
    rw [sum_eq_zero]
    intro k hk
    have : ¬(k = d ∧ p)
    push_neg; intro; exact hp
    rw [if_neg this]

theorem sum_intro' {α : Type _} [Ring α] (s : Finset ℕ) {f : ℕ → α} (d : ℕ)
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
  aesop_div
  
theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d in n.divisors,
        ∑ d1 in d.divisors,
          ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d in n.divisors,
        ∑ d1 in n.divisors,
          ∑ d2 in n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 :=
  by
  by_cases hn_zero : n = 0
  · rw [hn_zero]; simp
  rw [sum_congr rfl]; intro d hd
  have hdP_subset : divisors d ⊆ divisors n := 
    Nat.divisors_subset_of_dvd (hn_zero) (dvd_of_mem_divisors hd)
  rw [sum_subset hdP_subset, sum_congr rfl]; intro d1 hd1
  rw [sum_subset hdP_subset]
  · intro d2 hd2 hd2'
    rw [if_neg]; rw [Nat.lcm_comm]
    apply neq_lcm_of_ndvd' hd hd2'
  · intro d1 hd1 hd1'  
    rw [sum_eq_zero]; intro d2 hd2
    rw [if_neg]
    apply neq_lcm_of_ndvd' hd hd1'

theorem coprime_of_mul_squarefree (x y : ℕ) (h : Squarefree <| x * y) : x.coprime y :=
  by
  by_contra h_ncop
  rw [Nat.Prime.not_coprime_iff_dvd] at h_ncop 
  cases' h_ncop with p hp
  rcases hp with ⟨hpp, hpx, hpy⟩
  cases' hpx with r hx
  cases' hpy with s hy
  have : p * p ∣ x * y
  use r * s
  rw [hy]; rw [hx]; ring
  rw [Nat.squarefree_iff_prime_squarefree] at h 
  specialize h p hpp
  exact h this

theorem dvd_iff_mul_of_dvds {P : ℕ} (k d l m : ℕ) (hd : d ∈ P.divisors) :
    k = d / l ∧ l ∣ d ∧ d ∣ m ↔ d = k * l ∧ d ∣ m :=
  by
  constructor
  · intro h
    rcases h with ⟨hk_eq, hl_dvd_d, hd_dvd_m⟩
    constructor
    rw [hk_eq]; rw [eq_comm]
    exact Nat.div_mul_cancel hl_dvd_d
    exact hd_dvd_m
  · intro h
    cases' h with hd_eq hd_dvd_m
    constructor
    have : 0 < l := by
      rw [zero_lt_iff]
      simp at hd 
      by_contra h; rw [h] at hd_eq ; simp at hd_eq 
      rw [hd_eq] at hd ; simp at hd 
    rw [hd_eq]; rw [eq_comm]; exact Nat.mul_div_cancel k this
    constructor
    use k; rw [hd_eq]; ring
    exact hd_dvd_m

theorem divisors_filter_dvd {P : ℕ} (n : ℕ) (hP : P ≠ 0) (hn : n ∣ P) :
    (P.divisors.filter (· ∣ n)) = n.divisors :=
  by
  ext k; rw [mem_filter]; 
  aesop_div

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d in m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero $ Squarefree.ne_zero hm
  revert hm
  revert m
  rw [ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on_prop (fun n => Squarefree n) (fun _ _ => Squarefree.squarefree_of_dvd)]
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]-- 
  by_cases hl : l ∣ m
  swap
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd) 
  rw [if_pos hl, sum_eq_single l]
  · have hmul : m / l * l = m := Nat.div_mul_cancel hl
    rw [if_pos rfl, smul_eq_mul, ←Nat.ArithmeticFunction.IsMultiplicative.map_mul_of_coprime 
      Nat.ArithmeticFunction.isMultiplicative_moebius, hmul]
    apply coprime_of_mul_squarefree; rw [hmul]; exact hm
  · intro d _ hdl; rw[if_neg $ Ne.symm hdl, smul_zero]
  · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, Ne.symm $ Nat.ne_of_lt hm_pos⟩

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

theorem lcm_squarefree_of_squarefree {n m : ℕ} (hn : Squarefree n) (hm : Squarefree m) :
    Squarefree (n.lcm m) := by
  have hn_ne_zero := Squarefree.ne_zero hn
  have hm_ne_zero := Squarefree.ne_zero hm
  have hlcm_ne_zero := lcm_ne_zero hn_ne_zero hm_ne_zero
  rw [Nat.squarefree_iff_factorization_le_one hn_ne_zero] at hn
  rw [Nat.squarefree_iff_factorization_le_one hm_ne_zero] at hm 
  rw [Nat.squarefree_iff_factorization_le_one hlcm_ne_zero]
  rw [Nat.factorization_lcm hn_ne_zero hm_ne_zero]
  intro p
  rw [Finsupp.sup_apply, sup_le_iff]
  exact ⟨hn p, hm p⟩

example (n m : ℕ) (h : Squarefree (n * m)) : n.coprime m :=
  coprime_of_mul_squarefree n m h

theorem mult_gcd_lcm_of_squarefree (f : ℕ → ℝ) (h_mult : Multiplicative f) (x y : ℕ)
    (hx : Squarefree x) (hy : Squarefree y) : f x * f y = f (x.lcm y) * f (x.gcd y) :=
  by
  have hgcd : Squarefree (x.gcd y) := 
    by apply Squarefree.squarefree_of_dvd _ hx; exact Nat.gcd_dvd_left x y
  dsimp only [Nat.lcm]
  have hassoc : x * y / x.gcd y = x * (y / x.gcd y) := Nat.mul_div_assoc x (Nat.gcd_dvd_right x y)
  rw [hassoc]
  have hx_cop_yg : x.coprime (y / x.gcd y) :=
    by
    apply coprime_of_mul_squarefree
    rw [← hassoc]; exact lcm_squarefree_of_squarefree hx hy
  rw [h_mult.right x (y / x.gcd y) hx_cop_yg]
  have : (y / x.gcd y).coprime (x.gcd y) :=
    by
    apply coprime_of_mul_squarefree
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_right x y)]
    exact hy
  rw [mul_assoc]
  rw [← h_mult.right _ _ this]
  rw [Nat.div_mul_cancel (Nat.gcd_dvd_right x y)]

theorem mult_lcm_eq_of_ne_zero (f : ℕ → ℝ) (h_mult : Multiplicative f) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) (hx : Squarefree x) (hy : Squarefree y) : 
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [mult_gcd_lcm_of_squarefree f h_mult x y hx hy]
  rw [mul_div_assoc, div_self, mul_one]
  exact hf


theorem gcd_dvd_mul (m n : ℕ) : m.gcd n ∣ m * n := by
  calc
    m.gcd n ∣ m := Nat.gcd_dvd_left m n
    _ ∣ m * n := ⟨n, rfl⟩

theorem multiplicative_zero_of_zero_dvd (f : ℕ → ℝ) (h_mult : Multiplicative f) {m n : ℕ}
    (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 :=
  by
  cases' hmn with k hk
  rw [hk]
  rw [hk] at h_sq 
  have : m.coprime k := coprime_of_mul_squarefree m k h_sq
  rw [h_mult.right m k this]
  rw [h_zero]; simp only [MulZeroClass.zero_mul, eq_self_iff_true]

example (t : Finset ℕ) : t.val.prod = ∏ i in t, i :=
  prod_val t

theorem prod_subset_factors_of_mult (f : ℕ → ℝ) (h_mult : Multiplicative f) {l : ℕ}
    (hl : Squarefree l) :
    ∀ t : Finset ℕ, t ⊆ l.factors.toFinset → ∏ a : ℕ in t, f a = f t.val.prod :=
  by
  intro t; intro ht; rw [prod_val t];
  induction' t using Finset.induction_on with p t hpt h_ind 
  --intro h
  simp only [eq_self_iff_true, Finset.prod_empty, Finset.empty_val, Multiset.prod_zero, h_mult.left]
  --intro p t hpt h_ind h_sub
  have ht_sub : t ⊆ l.factors.toFinset := Finset.Subset.trans (Finset.subset_insert p t) ht
  have hl_primes : ∀ a : ℕ, a ∈ l.factors.toFinset → a.Prime :=
    by
    intro a hal
    rw [List.mem_toFinset] at hal 
    exact Nat.prime_of_mem_factors hal
  have ht_primes : ∀ a : ℕ, a ∈ t → a.Prime :=
    by
    intro a ha; apply hl_primes a
    apply mem_of_subset ht_sub ha
  have hp_prime : p.Prime :=
    by apply hl_primes p; apply mem_of_subset ht; exact mem_insert_self p t
  have hp_cop : p.coprime (t.prod _root_.id) :=
    by
    rw [Nat.Prime.coprime_iff_not_dvd hp_prime]
    rw [Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp_prime) _root_.id]
    push_neg; intro a ha; by_contra hpa
    rw [id.def] at hpa 
    have : p = a :=
      eq_comm.mp ((Nat.Prime.dvd_iff_eq (ht_primes a ha) (Nat.Prime.ne_one hp_prime)).mp hpa)
    rw [this] at hpt 
    exact hpt ha
  specialize h_ind ht_sub
  calc
    ∏ a : ℕ in insert p t, f a = f p * ∏ a : ℕ in t, f a := prod_insert hpt
    _ = f p * f (t.prod _root_.id) := by rw [h_ind]
    _ = f (p * ∏ a in t, a) := by rw [h_mult.right p (∏ a in t, a) hp_cop]; rfl
    _ = f (∏ a in insert p t, a) := by rw [prod_insert hpt]

theorem eq_prod_set_factors_of_squarefree {l : ℕ} (hl : Squarefree l) :
    l.factors.toFinset.val.prod = l :=
  by
  suffices l.factors.toFinset.val = l.factors 
    by rw [this]; rw [Multiset.coe_prod]; exact prod_factors (Squarefree.ne_zero hl)
  ext p
  rw [List.toFinset_val]
  rw [Multiset.coe_count]; rw [Multiset.coe_count]
  rw [List.count_dedup]
  rw [eq_comm]
  apply List.count_eq_of_nodup
  apply (squarefree_iff_nodup_factors _).mp hl
  exact Squarefree.ne_zero hl

theorem prod_factors_of_mult (f : ℕ → ℝ) (h_mult : Multiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a : ℕ in l.factors.toFinset, f a = f l :=
  by
  rw [prod_subset_factors_of_mult f h_mult hl l.factors.toFinset Finset.Subset.rfl]
  suffices : l.factors.toFinset.val.prod = l; rw [this]
  exact eq_prod_set_factors_of_squarefree hl

theorem prod_add_mult (f : ℕ → ℝ) (h_mult : Multiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, (1 + f p) = ∑ d in l.divisors, f d :=
  by
  conv =>
    lhs
    congr
    next => skip
    ext
    rw [add_comm]
  rw [Finset.prod_add]
  conv =>
    lhs
    congr
    next => skip
    ext
    conv =>
      congr
      next => skip
      rw [prod_eq_one fun _ _ => rfl]
    rw [mul_one]
  have : l.divisors.filter Squarefree = l.divisors :=
    by
    ext x; constructor
    apply filter_subset
    intro hx; simp only [Finset.mem_filter]; constructor
    exact hx; rw [mem_divisors] at hx ; exact Squarefree.squarefree_of_dvd hx.left hl
  conv =>
    rhs
    congr
    rw [← this]
  rw [Nat.sum_divisors_filter_squarefree]
  have hfact_eq :
    l.factors.toFinset.powerset =
      (UniqueFactorizationMonoid.normalizedFactors l).toFinset.powerset :=
    by rw [Nat.factors_eq]; simp
  apply sum_congr hfact_eq
  intro t ht
  rw [← hfact_eq] at ht 
  rw [mem_powerset] at ht 
  exact prod_subset_factors_of_mult f h_mult hl t ht
  exact Squarefree.ne_zero hl

theorem prod_eq_moebius_sum (f : ℕ → ℝ) (h_mult : Multiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ p in l.factors.toFinset, (1 - f p) = ∑ d in l.divisors, μ d * f d :=
  by
  suffices
    ∏ p in l.factors.toFinset, ((1 : ℝ) + (fun x : ℕ => (μ x : ℝ) * f x) p) =
      ∑ d in l.divisors, μ d * f d
    by
    rw [← this]
    apply prod_congr rfl; intro p hp
    rw [List.mem_toFinset] at hp 
    have hp_prime : p.Prime := by apply prime_of_mem_factors hp
    
    suffices 1 - f p = 1 + ↑(μ p) * f p 
      by exact this
    rw [ArithmeticFunction.moebius_apply_prime hp_prime] ; push_cast ; ring 

  apply prod_add_mult
  constructor
  suffices (μ 1 : ℝ) * f 1 = 1 
    by exact this
  rw [ArithmeticFunction.moebius_apply_one]
  rw [h_mult.left]; push_cast ; ring
  intro a b hab
  suffices (μ (a * b) : ℝ) * f (a * b) = μ a * f a * (μ b * f b)
    by exact this
  rw [ArithmeticFunction.isMultiplicative_moebius.right hab]
  rw [h_mult.right a b hab]; push_cast ; ring
  exact hl

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
    · intro n hn; apply hg; rw [mem_insert]; exact Or.intro_right (n = q) hn
    · intro n hn; apply hf; rw [mem_insert]; exact Or.intro_right (n = q) hn
    · intro n hn; apply hfg; rw [mem_insert]; exact Or.intro_right (n = q) hn
  · suffices : s = ∅; rw [this]; simp only [le_refl, Finset.prod_empty]
    rw [not_nonempty_iff_eq_empty] at hs_ne ; exact hs_ne
  apply prod_pos; intro p hps; apply hf p; rw [mem_insert]; exact Or.intro_right (p = q) hps
  apply le_of_lt; exact hg q hq_in

theorem div_mult_of_dvd_squarefree (f : ℕ → ℝ) (h_mult : Multiplicative f) (l d : ℕ) (hdl : d ∣ l)
    (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) :=
  by
  apply div_eq_of_eq_mul hd
  have : l / d * d = l := by apply Nat.div_mul_cancel hdl
  rw [← h_mult.right]
  rw [this]
  apply coprime_of_mul_squarefree
  rw [this]; exact hl

theorem div_mult_of_mult {f g : ℕ → ℝ} (hf : Multiplicative f) (hg : Multiplicative g)
    (hg_zero : ∀ n : ℕ, 0 < n → g n ≠ 0) : Multiplicative (f / g) :=
  by
  constructor
  calc
    (f / g) 1 = f 1 / g 1 := rfl
    _ = 1 := by rw [hf.left]; rw [hg.left]; ring
  intro x y hxy
  calc
    (f / g) (x * y) = f (x * y) / g (x * y) := rfl
    _ = f x * f y / (g x * g y) := by rw [hf.right x y hxy]; rw [hg.right x y hxy]
    _ = f x / g x * (f y / g y) := by rw [← div_div]; ring
    _ = (f / g) x * (f / g) y := rfl

theorem coe_mult : Multiplicative fun n : ℕ => (n : ℝ) :=
  by
  constructor; exact Nat.cast_one
  intro x y _
  exact cast_mul x y
  
theorem mult_mul_of_mult (f g : ℕ → ℝ) (hf : Multiplicative f) (hg : Multiplicative g) :
    Multiplicative (f * g) := by
  constructor
  suffices f 1 * g 1 = 1  
    by exact this
  rw [hf.left]; rw [hg.left]; ring
  intro x y hxy
  suffices (f <| x * y) * (g <| x * y) = f x * g x * (f y * g y)
    by exact this 
  rw [hf.right x y hxy];
  rw [hg.right x y hxy]; ring

theorem mult_prod_factors (f : ℕ → ℝ) : Multiplicative fun d => ∏ p in d.factors.toFinset, f p :=
  by
  constructor
  simp
  intro x y hxy
  simp
  have h_union : (x * y).factors.toFinset = x.factors.toFinset ∪ y.factors.toFinset :=
    by
    ext p; rw [List.mem_toFinset]; rw [← List.toFinset_union]; rw [List.mem_toFinset]
    exact Nat.mem_factors_mul_of_coprime hxy p
  have h_disj : Disjoint x.factors.toFinset y.factors.toFinset := by
    rw [List.disjoint_toFinset_iff_disjoint]; exact Nat.coprime_factors_disjoint hxy
  rw [← Finset.prod_disjUnion h_disj]; rw [Finset.disjUnion_eq_union]; rw [h_union]

theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 :=
  by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hl]
  rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]

theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 :=
  by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hl]
  rw [abs_pow]; simp

theorem eq_one_of_prod_eq_one {α : Type _} (s : Finset α) (f : α → ℕ) (hp : ∏ i in s, f i = 1) :
    ∀ i ∈ s, f i = 1 := by
  --revert hp
  induction' s using Finset.induction_on with j s hj h_ind 
  simp
  intros i hi
  --intro j s hj h_ind heq_one i hi
  rw [Finset.prod_insert hj] at hp 
  rw [mem_insert] at hi 
  cases' hi with hi hi
  · rw [hi]; exact Nat.eq_one_of_mul_eq_one_right hp
  exact h_ind (Nat.eq_one_of_mul_eq_one_left hp) i hi

theorem fintype_eq_one_of_prod_eq_one {α : Type _} [Fintype α] (f : α → ℕ)
    (hp : ∏ i in Finset.univ, f i = 1) : ∀ i, f i = 1 :=
  by
  intro i
  apply eq_one_of_prod_eq_one Finset.univ f hp
  exact mem_univ i

theorem prime_dvd_prod {α : Type _} {p : ℕ} (hp : p.Prime) {s : Finset α} (f : α → ℕ)
    (h_prod : p ∣ ∏ i in s, f i) : ∃ i, p ∣ f i :=
  by
  --revert h_prod
  induction' s using Finset.induction_on with a s ha hi
  rw [prod_empty] at h_prod; exfalso; rw [Nat.dvd_one] at h_prod;
  exact Nat.Prime.ne_one hp h_prod
  --intro a s ha ih hprod
  rw [prod_insert ha, Nat.Prime.dvd_mul hp] at h_prod 
  cases' h_prod with h_prod h_prod
  use a; exact h_prod 
  exact hi h_prod

theorem cardDistinctFactors_eq_cardFactors_of_squarefree {n : ℕ} (hn : Squarefree n) : ω n = Ω n :=
  (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree <|
        Squarefree.ne_zero hn).mpr
    hn

@[simp]
def tuplesWithProd (h d P : ℕ) : Finset (Fin h → ℕ) :=
  (Fintype.piFinset fun i : Fin h => P.divisors).filter fun s : Fin h → ℕ => ∏ i, s i = d

@[simp]
def mem_tuplesWithProd {h d P : ℕ} {s : Fin h → ℕ} :
    s ∈ tuplesWithProd h d P ↔ (∀ i, s i ∈ P.divisors) ∧ ∏ i, s i = d :=
  by
  dsimp only [tuplesWithProd]
  rw [mem_filter, Fintype.mem_piFinset]

-- Perhaps there is a better way to do this with partitions, but the proof isn't too bad
-- |{(d1, ..., dh) : d1*...*dh = d}| = h^ω(d)
theorem card_tuplesWithProd {P d : ℕ} (hP : Squarefree P) (hdP : d ∣ P) (h : ℕ) :
    (tuplesWithProd h d P).card = h ^ ω d :=
  by
  revert hdP
  dsimp only [tuplesWithProd]
  induction' d using Nat.strong_induction_on with d h_ind
  --apply Nat.strong_induction_on d
  --clear d; intro d
  intro hdP
  have hd_sqfree : Squarefree d := Squarefree.squarefree_of_dvd hdP hP
  have hd_zero : d ≠ 0 := Squarefree.ne_zero hd_sqfree
  have hP_ne_zero : P ≠ 0 := Squarefree.ne_zero hP
  by_cases h_1 : d = 1
  · rw [h_1];
    rw [show h ^ ω 1 = 1 by
        simp only [eq_self_iff_true, Nat.pow_zero, Nat.ArithmeticFunction.cardDistinctFactors_one]]
    apply card_eq_one.mpr; use fun _ => 1
    ext a; rw [mem_singleton, mem_filter, Fintype.mem_piFinset]; constructor
    · intro h; ext x; apply fintype_eq_one_of_prod_eq_one a h.right
    · intro h; rw [h]; constructor; intro i; rw [one_mem_divisors]; exact Squarefree.ne_zero hP
      apply prod_eq_one; intro _ _; rfl
  have := exists_prime_and_dvd h_1
  rcases this with ⟨p, ⟨hp_prime, hp_dvd⟩⟩
  let S := tuplesWithProd h d P
  let Sp_dvd : Fin h → Finset _ := fun j => S.filter fun s : Fin h → ℕ => p ∣ s j
  have hunion : Finset.univ.biUnion Sp_dvd = S :=
    by
    ext s; rw [mem_biUnion]; constructor
    · rintro ⟨i, _, hi⟩; rw [mem_filter] at hi ; exact hi.1
    intro hs
    rw [mem_tuplesWithProd] at hs 
    rw [← hs.2] at hp_dvd 
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
      apply coprime_of_mul_squarefree
      apply Squarefree.squarefree_of_dvd _ hd_sqfree
      calc
        t i * t j ∣ t i * t j * ∏ k in (univ.erase i).erase j, t k :=
          ⟨∏ k in (univ.erase i).erase j, t k, rfl⟩
        _ = t i * ∏ k in univ.erase i, t k :=
          by
          rw [mul_assoc, mul_prod_erase]
          rw [mem_erase]
          exact ⟨ne_comm.mp hij, mem_univ j⟩
        _ = d := by rw [mul_prod_erase _ _ (mem_univ i), hs.1.2]
    apply absurd this
    rw [Nat.Prime.not_coprime_iff_dvd]
    use p; exact ⟨hp_prime, hs.2, ht.2⟩
  dsimp at hunion hdisj
  rw [←hunion]
  rw [Finset.card_biUnion hdisj]
  cases' hp_dvd with k hk
  have hp_dvd : p ∣ d := by use k; exact hk
  have hp_ne_zero : p ≠ 0 := ne_zero_of_dvd_ne_zero hd_zero hp_dvd
  have hp_pos : 0 < p := zero_lt_iff.mpr hp_ne_zero
  let f : Fin h → ∀ s : Fin h → ℕ, s ∈ tuplesWithProd h k P → Fin h → ℕ := fun i s hs => fun j =>
    if i = j then p * s j else s j
  have himg : ∀ (i s) (hs : s ∈ tuplesWithProd h k P), f i s hs ∈ Sp_dvd i :=
    by
    intro i s hs
    rw [mem_tuplesWithProd] at hs 
    rw [mem_filter, mem_tuplesWithProd]; dsimp only [tuplesWithProd]; constructor; constructor
    intro j
    by_cases hij : i = j
    · rw [if_pos hij]
      rw [mem_divisors]
      constructor
      calc
        p * s j ∣ p * ∏ j, s j := by
          rw [mul_dvd_mul_iff_left hp_ne_zero]
          apply Finset.dvd_prod_of_mem s (mem_univ j)
        _ = d := by rw [hs.2, hk]
        _ ∣ P := hdP
      exact hP_ne_zero
    · rw [if_neg hij]; exact hs.1 j
    calc
      ∏ j : Fin h, ite (i = j) (p * s j) (s j) = p * s i * ∏ j in univ.erase i, s j :=
        by
        rw [← mul_prod_erase univ _ (mem_univ i)]
        rw [if_pos rfl]
        apply congr_arg fun x => p * s i * x
        apply prod_congr rfl; intro j hj
        rw [mem_erase, ne_comm] at hj 
        rw [if_neg hj.1]
      _ = d := by rw [mul_assoc, mul_prod_erase _ _ (mem_univ i), hs.2, hk]
    rw [if_pos rfl]; use s i
  have hinj :
    ∀ (i s t) (hs : s ∈ tuplesWithProd h k P) (ht : t ∈ tuplesWithProd h k P),
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
    ∀ (i t) (ht : t ∈ Sp_dvd i), ∃ (s : _) (hs : s ∈ tuplesWithProd h k P), f i s hs = t :=
    by
    intro i t ht
    rw [mem_filter] at ht ; dsimp only []
    dsimp only [] at ht  
    rw [mem_tuplesWithProd] at ht 
    let s j := if i = j then t j / p else t j
    use s; constructor; swap
    rw [mem_tuplesWithProd]; constructor
    intro j
    dsimp only []
    by_cases hij : i = j
    · rw [if_pos hij]
      rw [mem_divisors]
      constructor; rw [← hij]
      calc
        _ ∣ t i := div_dvd_of_dvd ht.2
        _ ∣ P := (mem_divisors.mp (ht.1.1 i)).1
      exact Squarefree.ne_zero hP
    · rw [if_neg hij]; exact ht.1.1 j
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
      _ = d / p := by rw [Finset.mul_prod_erase univ t (mem_univ i), ht.1.2]
      _ = k := by rw [hk]; exact Nat.mul_div_cancel_left k hp_pos
    funext j
    dsimp only []
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, Nat.mul_div_cancel']
      rw [← hij]; exact ht.2
    · rw [if_neg hij, if_neg hij]
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP hP
  have hk_dvd : k ∣ d := by use p; rw [mul_comm]; exact hk
  have hk_sq : Squarefree k := Squarefree.squarefree_of_dvd hk_dvd hd_sq
  calc
    ∑ i, (Sp_dvd i).card = ∑ i : Fin h, (tuplesWithProd h k P).card :=
      by
      apply sum_congr rfl; intro i _; rw [eq_comm]
      apply Finset.card_congr (f i) (himg i) (hinj i) (hsurj i)
    _ = h ^ ω d := by
      rw [Fin.sum_const]
      dsimp only [tuplesWithProd]
      rw [h_ind k _ _, smul_eq_mul, ←_root_.pow_succ]
      rw [cardDistinctFactors_eq_cardFactors_of_squarefree hd_sq,
        cardDistinctFactors_eq_cardFactors_of_squarefree hk_sq, ←
        ArithmeticFunction.cardFactors_apply_prime hp_prime, ←
        Nat.ArithmeticFunction.cardFactors_mul, mul_comm, hk]
      exact Squarefree.ne_zero hk_sq; exact Nat.Prime.ne_zero hp_prime
      apply lt_of_le_of_ne; apply le_of_dvd _ hk_dvd; rw [zero_lt_iff]; exact hd_zero
      rw [← one_mul k, hk]; apply Nat.ne_of_lt; apply mul_lt_mul; exact Prime.one_lt hp_prime
      exact le_rfl; rw [zero_lt_iff]; exact Squarefree.ne_zero hk_sq
      exact Nat.zero_le p
      calc
        k ∣ d := by use p; rw [hk]; ring
        _ ∣ P := hdP

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
  rw [← card_tuplesWithProd hn dvd_rfl 3, eq_comm]
  have hn_ne_zero : n ≠ 0 := Squarefree.ne_zero hn
  let f : ∀ (a : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd 3 n n), ℕ × ℕ := fun a ha =>
    (a 0 * a 1, a 0 * a 2)
  have hprod : ∀ (a : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd 3 n n), a 0 * a 1 * a 2 = n :=
    by
    intro a ha; rw [mem_tuplesWithProd] at ha 
    rw [← ha.2, prod3 a]
  have ha_ne_zero : ∀ (a : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd 3 n n) (i : Fin 3), a i ≠ 0 :=
    by
    intro a ha i; rw [mem_tuplesWithProd] at ha 
    by_contra hai
    rw [Finset.prod_eq_zero (mem_univ i) hai] at ha 
    exact hn_ne_zero (eq_comm.mp ha.2)
  have h_img :
    ∀ (a : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd 3 n n),
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
    apply coprime_of_mul_squarefree
    apply Squarefree.squarefree_of_dvd _ hn
    calc
      a 1 * a 2 ∣ a 0 * a 1 * a 2 := by use a 0; ring
      _ = n := hprod a ha
  have h_inj :
    ∀ (a b : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd 3 n n) (hb : b ∈ tuplesWithProd 3 n n),
      f a ha = f b hb → a = b :=
    by
    intro a b ha hb hfab
    dsimp only [] at hfab 
    cases' Prod.mk.inj hfab with hfab1 hfab2
    have hab2 : a 2 = b 2 :=
      by
      have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2
      conv =>
        rhs
        rw [hfab1]
      rw [hprod a ha, hprod b hb]
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
        ∃ (a : Fin 3 → ℕ) (ha : a ∈ tuplesWithProd 3 n n), f a ha = b :=
    by
    intro b hb
    let g := b.fst.gcd b.snd
    let a := fun i : Fin 3 => if i = 0 then g else if i = 1 then b.fst / g else b.snd / g
    have ha : a ∈ tuplesWithProd 3 n n :=
      by
      rw [mem_tuplesWithProd]
      rw [mem_filter, Finset.mem_product] at hb 
      have hbfst_dvd : b.fst ∣ n := (mem_divisors.mp hb.1.1).1
      have hbsnd_dvd : b.snd ∣ n := (mem_divisors.mp hb.1.2).1
      constructor
      intro i; rw [mem_divisors]; fin_cases i
      exact ⟨Trans.trans (Nat.gcd_dvd_left b.fst b.snd) (hbfst_dvd), hn_ne_zero⟩
      constructor
      calc
        b.fst / g ∣ b.fst := div_dvd_of_dvd (Nat.gcd_dvd_left b.fst b.snd)
        _ ∣ n := hbfst_dvd
      exact hn_ne_zero
      constructor
      calc
        b.snd / g ∣ b.snd := div_dvd_of_dvd (Nat.gcd_dvd_right b.fst b.snd)
        _ ∣ n := hbsnd_dvd
      exact hn_ne_zero
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

theorem nat_sq_mono {a b : ℕ} (h : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  pow_mono_right 2 h

example (x : ℝ) (hx : 0 < x) : ∫ t : ℝ in (1)..x, 1 / t = Real.log x :=
  by
  rw [integral_one_div_of_pos, div_one]
  linarith; assumption

example (a b : ℕ) (h : a ≤ b) : Ico a (b + 1) = Icc a b :=
  rfl

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

#check fun n : ℕ => ∫ x in (2 : ℝ)..(n + 1 : ℝ), 1 / (x - 1)
#exit
-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d in P.divisors, if ↑d ≤ x then h ^ (ω d:ℕ) / (d : ℝ) else (0 : ℝ)) ≤ (1 + Real.log x) ^ h :=
  by
  by_cases hP_zero : P = 0
  · rw [hP_zero]; simp; apply pow_nonneg; sorry
  calc
    _ = ∑ d in P.divisors, ite (↑d ≤ x) (↑(tuplesWithProd h d P).card / (d : ℝ)) 0 := ?_
    _ = ∑ d in P.divisors, ↑(tuplesWithProd h d P).card * ite (↑d ≤ x) (1 / (d : ℝ)) 0 := ?_
    _ =
        ∑ d in P.divisors,
          ∑ a in Fintype.piFinset fun i : Fin h => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then 1 / (d : ℝ) else 0 else 0 := ?_
    _ =
        ∑ a in Fintype.piFinset fun i : Fin h => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, 1 / (a i : ℝ) else 0 else 0 := ?_
    _ ≤
        ∑ a in Fintype.piFinset fun i : Fin h => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, 1 / (a i : ℝ) else 0 := ?_
    _ ≤
        ∑ a in Fintype.piFinset fun i : Fin h => P.divisors,
          ∏ i, if ↑(a i) ≤ x then 1 / (a i : ℝ) else 0 := ?_
    _ = ∏ i : Fin h, ∑ d in P.divisors, if ↑d ≤ x then 1 / (d : ℝ) else 0 := ?_
    _ = (∑ d in P.divisors, if ↑d ≤ x then 1 / (d : ℝ) else 0) ^ h := ?_
    _ ≤ (1 + Real.log x) ^ h := ?_
  · apply sum_congr rfl; intro d hd; apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
    intro; norm_cast; rw [← card_tuplesWithProd hP (mem_divisors.mp hd).1 h]
  · apply sum_congr rfl; intro d hd; rw [← ite_mul_zero_right]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
    intro _; rw [mul_one_div]
  · apply sum_congr rfl; intro d hd
    rw [Finset.card_eq_sum_ones, cast_sum, cast_one, sum_mul, one_mul]
    dsimp only [tuplesWithProd]; rw [sum_filter]; apply sum_congr rfl; intro a ha
    have : ∏ i, a i = d ↔ ∏ i, a i = d ∧ d ∣ P := 
      by rw [mem_divisors] at hd ; rw [iff_self_and]; exact fun _ => hd.1
    rw [if_ctx_congr this (fun _ => rfl) (fun _ => rfl)]
  · rw [sum_comm]; apply sum_congr rfl; intro a ha; rw [sum_eq_single (∏ i, a i)]
    apply if_ctx_congr _ _ (fun _ => rfl); rw [Iff.comm, iff_and_self]; exact fun _ => rfl
    intro; rw [one_div, cast_prod, ← prod_inv_distrib, if_ctx_congr Iff.rfl _ (fun _ => rfl)]
    intro; apply prod_congr rfl; intro _ _; rw [one_div]
    intro d hd hd_ne; rw [ne_comm] at hd_ne ; rw [if_neg]; by_contra h; exact hd_ne h.1
    intro h; rw [if_neg]; by_contra h_cont; rw [mem_divisors] at h ; sorry
  repeat' sorry

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d in P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤ x * (1 + Real.log x) ^ h :=
  sorry

end Aux

