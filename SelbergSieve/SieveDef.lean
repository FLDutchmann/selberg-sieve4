/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Squarefree
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction
import SelbergSieve.AuxResults
import SelbergSieve.LambdaSquaredDef

noncomputable section

open scoped BigOperators Classical Nat.ArithmeticFunction

open Finset Real Nat Aux

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

set_option profiler true


structure Sieve where mk ::
  support : Finset ℕ
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  weights : ℕ → ℝ
  ha_nonneg : ∀ n : ℕ, 0 ≤ weights n
  totalMass : ℝ
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ P → 0 < nu p
  nu_lt_self_of_prime : ∀ p : ℕ, p.Prime → p ∣ P → nu p < p

namespace Sieve

pp_extended_field_notation nu
pp_extended_field_notation prodPrimes
pp_extended_field_notation weights
pp_extended_field_notation totalMass


set_option quotPrecheck false
variable (s : Sieve)
local notation "ν" => s.nu
local notation "P" => s.prodPrimes
local notation "a" => s.weights
local notation "X" => s.totalMass

@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n in s.support, if d ∣ n then a n else 0

-- A_d = ν (d)/d X + R_d
@[simp]
def rem (d : ℕ) : ℝ :=
  s.multSum d - ν d / d * X

local notation "R" => s.rem
pp_extended_field_notation rem

def siftedSum : ℝ :=
  ∑ d in s.support, if coprime P d then a d else 0

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound
def selbergTerms (d : ℕ) : ℝ :=
  ν d / d * ∏ p in d.factors.toFinset, 1 / (1 - ν p / p)

local notation "g" => s.selbergTerms
pp_extended_field_notation selbergTerms

def mainSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d in divisors P, μPlus d * (ν d / d)

def errSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d in divisors P, |μPlus d| * |R d|

end Sieve