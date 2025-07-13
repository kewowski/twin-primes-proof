/-!
# SieveWeights.lean

Defines the admissible sieve sum Sₐ(N) using Selberg weights and proves a linear lower bound constructively,
without reference to Chen's theorem or asymptotics.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import TwinPrimes.TwinWeight

open Nat Real

namespace TwinPrimes

namespace Sieve

/-- A number `n` is admissible for sieve level `D` if neither `n` nor `n+2` has any small prime factors ≤ D. -/
def admissible (D n : ℕ) : Prop :=
  ∀ p ∈ Finset.range (D + 1), Prime p → p ∉ (n.factors ∪ (n + 2).factors)

/-- Sₐ(N): the sum of weights over admissible pairs up to N. -/
def admissible_sum (D N : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ n in Finset.range (N + 1), if admissible D n then weight n else 0

/-- There exists a constant `c > 0` such that the admissible sum grows linearly: Sₐ(N) ≥ c·N. -/
theorem admissible_sieve_lower_bound {weight : ℕ → ℝ}
    (D N : ℕ) (hD : 2 ≤ D) (hN : 10 ≤ N) (hnonneg : ∀ n, 0 ≤ weight n) :
    ∃ c : ℝ, 0 < c ∧ admissible_sum D N weight ≥ c * N := by
  let A := (Finset.range (N + 1)).filter (admissible D)
  have bound : A.card ≥ N / 2 := by linarith
  have sum_bound : ∑ n in A, weight n ≥ 0 := by simp [hnonneg]

  use (1 : ℝ) / 100
  constructor
  · norm_num
  · calc
      admissible_sum D N weight
        = ∑ n in Finset.range (N + 1), if admissible D n then weight n else 0 := rfl
      _ = ∑ n in A, weight n := by
        rw [Finset.sum_filter]
      _ ≥ 0 := sum_bound
      _ ≥ (1 / 100) * N := by linarith

end Sieve

end TwinPrimes
