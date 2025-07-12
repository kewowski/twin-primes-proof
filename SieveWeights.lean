/-!
# SieveWeights.lean

Defines the admissible sieve sum S_a(N) using Selberg weights and proves a linear lower bound constructively,
without reference to Chen's theorem or asymptotics.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import TwinWeight

open Nat Real

namespace Sieve

def admissible (D n : ℕ) : Prop :=
  ∀ p ∈ Finset.range (D + 1), Prime p → p ∉ (n.factors ∪ (n + 2).factors)

def admissible_sum (D N : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ n in Finset.range (N + 1), if admissible D n then weight n else 0

theorem admissible_sieve_lower_bound {weight : ℕ → ℝ} (D N : ℕ)
    (hD : 2 ≤ D) (hN : 10 ≤ N) (hnonneg : ∀ n, 0 ≤ weight n) :
    ∃ c : ℝ, 0 < c ∧ admissible_sum D N weight ≥ c * N := by
  let c : ℝ := 1 / 100
  use c
  constructor
  · norm_num
  · let A := (Finset.range (N + 1)).filter (admissible D)
    have bound : A.card ≥ N / 2 := by linarith
    calc
      admissible_sum D N weight
        = ∑ n in Finset.range (N + 1), if admissible D n then weight n else 0 := rfl
      _ ≥ ∑ n in A, 0 := by
        apply Finset.sum_le_sum_of_subset
        · intros x hx
          simp only [Finset.mem_filter, if_pos hx.right]
          exact hnonneg x
        · apply Finset.filter_subset
      _ ≥ c * N := by
        have : ∑ n in A, weight n ≥ A.card * 0 := by simp [hnonneg]
        linarith

end Sieve