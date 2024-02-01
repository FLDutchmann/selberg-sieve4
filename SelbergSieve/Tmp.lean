import Mathlib

noncomputable def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter (Nat.Prime) |>.card

theorem primesBetween_le {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1+Real.log z)^3 := sorry
