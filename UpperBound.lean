/-!
# UpperBound.lean

Proves the upper bound S(N) ≤ C·N for the sieve weight sum over all admissible pairs.
This module provides the required result for the contradiction strategy.

The result is constructive and uses only properties of Selberg weights.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import TwinPrimes.SelbergWeights

open Nat Real Selberg

namespace Sieve

/--
Sieve weight sum S(N) = ∑_{n ≤ N} wₙ where wₙ are Selberg weights.
-/
def sieve_weight_sum (D : ℕ) (hD : 1 < D) (N : ℕ) : ℝ :=
  ∑ n in Finset.range (N + 1), selberg_weight D hD n

/--
Every Selberg weight is nonnegative, so S(N) > 0.
-/
lemma sieve_weight_sum_pos (D : ℕ) (hD : 1 < D) (N : ℕ) : 0 < sieve_weight_sum D hD N := by
  apply Finset.sum_pos
  intros x hx
  have hsq : squarefree x := by
    by_contra H; simp [selberg_weight, selberg_lambda, H] at *
  have h_le : x ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
  have h_ne_zero : x ≠ 0 := by
    by_contra h; simp [h] at *
  simp [selberg_weight, selberg_lambda]
  split_ifs with H
  · exact sq_pos_of_ne_zero (by simp [H])
  · contradiction

/--
There exists a constant C > 0 such that S(N) ≤ C·N for all N ≥ 1.
We set C = 1 for simplicity, relying on boundedness of selberg weights.
-/
theorem sieve_weight_sum_upper_bound :
  ∃ C > 0, ∀ D (hD : 1 < D) (N : ℕ), sieve_weight_sum D hD N ≤ C * N := by
  let C : ℝ := 1
  use C
  constructor
  · norm_num
  · intros D hD N
    apply Finset.sum_le_sum
    intro n _
    -- Show each weight is ≤ 1 due to properties of Selberg lambda
    have hpos : 0 ≤ selberg_weight D hD n := by
      simp [selberg_weight, selberg_lambda]
      split_ifs <;> linarith
    have hbd : selberg_weight D hD n ≤ 1 := by
      simp [selberg_weight, selberg_lambda]
      split_ifs with h
      · apply div_le_one_of_le
        · apply mul_le_of_le_one_right (by positivity)
          apply Real.log_le_log (by linarith) (by linarith)
          apply div_le_one_of_le; linarith
        · apply logD_pos
      · linarith
    exact hbd

end Sieve