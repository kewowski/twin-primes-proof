/-!
# TwinWeight.lean

Defines the twin prime indicator function `Lambda2` and constructs the weighted sum `W(N)`
over actual twin primes using Selberg sieve weights.

All definitions are constructive and verified without asymptotics.
-/

import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import SelbergWeights

open Nat Selberg

namespace Twin

/--
Indicator function for twin primes: returns 1 if both n and n+2 are prime, 0 otherwise.
-/
def Lambda2 (n : ℕ) : ℕ :=
  if Prime n ∧ Prime (n + 2) then 1 else 0

@[simp]
lemma Lambda2_nonzero_iff {n : ℕ} :
    Lambda2 n ≠ 0 ↔ Prime n ∧ Prime (n + 2) := by
  simp [Lambda2]; split_ifs <;> simp [*]

/--
Twin prime weight: Λ₂(n) · w_n where w_n is the Selberg sieve weight.
-/
def twin_weight (D : ℕ) (hD : 1 < D) (n : ℕ) : ℝ :=
  (Lambda2 n : ℝ) * selberg_weight D hD n

/--
Weighted sum over twin primes up to N: W(N) := ∑_{n ≤ N} Λ₂(n) · w_n.
-/
def twin_weight_sum (D N : ℕ) (hD : 1 < D) : ℝ :=
  ∑ n in Finset.range (N + 1), twin_weight D hD n

@[simp]
lemma twin_weight_zero_of_not_twin {D n : ℕ} (hD : 1 < D) (h : ¬(Prime n ∧ Prime (n + 2))) :
    twin_weight D hD n = 0 := by
  simp [twin_weight, Lambda2, h]

lemma twin_weight_pos_iff {D n : ℕ} (hD : 1 < D) :
    0 < twin_weight D hD n ↔ Prime n ∧ Prime (n + 2) ∧ 0 < selberg_weight D hD n := by
  simp [twin_weight, Lambda2]; split_ifs with h
  · simp [h]
  · simp [Nat.not_and_of_not_right] at h; simp [h]

end Twin