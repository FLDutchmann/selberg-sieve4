import Mathlib.NumberTheory.ArithmeticFunction

open Finset
open scoped BigOperators Nat.ArithmeticFunction Classical 
set_option profiler true

namespace ArithmeticFunction

/-- Temporary: 
Möbius inversion for functions to an `add_comm_group`, where the equalities only hold on values
satisfying a well-behaved property. -/
theorem sum_eq_iff_sum_smul_moebius_eq_on_prop [AddCommGroup R] {f g : ℕ → R}
    (P : ℕ → Prop) (hP : ∀ m n, m ∣ n → P n → P m) :
    (∀ n : ℕ, 0 < n → P n → (∑ i in n.divisors, f i) = g n) ↔
      ∀ n : ℕ, 0 < n → P n → (∑ x : ℕ × ℕ in n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  constructor
  · intro h
    let G := fun (n:ℕ) => (∑ i in n.divisors, f i)
    intro n hn hnP
    suffices ∑ d in n.divisors, μ (n/d) • G d = f n from by
      rw [Nat.sum_divisorsAntidiagonal' (f:= fun x y => μ x • g y), ←this, sum_congr rfl]
      intro d hd
      rw [←h d (Nat.pos_of_mem_divisors hd) $ hP d n (Nat.dvd_of_mem_divisors hd) hnP]
    rw [←Nat.sum_divisorsAntidiagonal' (f:= fun x y => μ x • G y)]
    apply Nat.ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.mp _ n hn
    intro _ _; rfl
  · intro h
    let F := fun (n:ℕ) => ∑ x : ℕ × ℕ in n.divisorsAntidiagonal, μ x.fst • g x.snd
    intro n hn hnP
    suffices ∑ d in n.divisors, F d = g n from by
      rw [←this, sum_congr rfl]
      intro d hd
      rw [←h d (Nat.pos_of_mem_divisors hd) $ hP d n (Nat.dvd_of_mem_divisors hd) hnP]
    apply Nat.ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.mpr _ n hn
    intro _ _; rfl


/-- Möbius inversion for functions to a `Ring`, where the equalities only hold on values satisfying
a well-behaved property. -/
theorem sum_eq_iff_sum_mul_moebius_eq_on_prop [Ring R] {f g : ℕ → R}
    (P : ℕ → Prop) (hP : ∀ m n, m ∣ n → P n → P m) :
    (∀ n : ℕ, 0 < n → P n → (∑ i in n.divisors, f i) = g n) ↔
      ∀ n : ℕ, 0 < n → P n →
        (∑ x : ℕ × ℕ in n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd) = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq_on_prop P hP]
  apply forall_congr'
  intro a; refine' imp_congr_right _
  refine' fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => _).congr_left
  rw [zsmul_eq_mul]
end ArithmeticFunction