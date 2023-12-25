import SelbergSieve.PrimeCountingUpperBound

open Nat ArithmeticFunction PrimeUpperBound

namespace Nat

def TwinPrime (n : ℕ) : Prop := n.Prime ∧ ((n-2).Prime ∨ (n+2).Prime)


instance (n : ℕ) : Decidable (TwinPrime n) :=
  And.decidable


example : TwinPrime 5 := by
  decide

def twinPrimeCounting' : ℕ → ℕ := Nat.count TwinPrime

def twinPrimeCounting (n : ℕ) := twinPrimeCounting' (n+1)

scoped[Nat.TwinPrime] notation "π₂" => Nat.twinPrimeCounting

scoped[Nat.TwinPrime] notation "π₂'" => Nat.twinPrimeCounting'

noncomputable def twinPrimeSieve (N : ℕ) (y : ℝ) (hy : 1 ≤ y): SelbergSieve := {
  support := (Finset.range (N + 1)).image (fun n ↦ n * (n+2))
  prodPrimes := primorial (Nat.floor y)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  ha_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := ζ
  nu_mult := Nat.ArithmeticFunction.isMultiplicative_zeta.nat_cast
  nu_pos_of_prime := fun p hp _ => zeta_pos_of_prime p hp
  nu_lt_self_of_prime := fun p hp _ => zeta_lt_self_of_prime p hp
  level := y
  one_le_level := hy
}

noncomputable def f : Polynomial ℤ := .X * (.X+2)

example (p : ℕ) : (ℤ →+* ZMod p) := by exact Int.castRingHom (ZMod p)

#check f.map (Int.castRingHom (ZMod 3))

end Nat
