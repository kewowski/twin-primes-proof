/-!
# SelbergWeights.lean

Defines the Selberg sieve weight function `selberg_lambda` for squarefree divisors `d ≤ D`,
and proves basic support, vanishing, and normalization properties.
-/

import Mathlib.Data.Nat.Multiplicity
import Mathlib.NumberTheory.MoebiusFunction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat

namespace TwinPrimes

namespace Selberg

variable (D : ℕ) (hD : 1 < D)

lemma logD_pos : 0 < Real.log D :=
  Real.log_pos (by linarith)

/-- Selberg sieve coefficient λ_d = μ(d) · log(D / d) / log D, defined only for squarefree d ≤ D. -/
def selberg_lambda (d : ℕ) : ℝ :=
  if d = 0 ∨ ¬ squarefree d ∨ d > D then 0
  else (moebius d : ℝ) * Real.log (D / d) / Real.log D

lemma lambda_vanishes (d : ℕ) (h : d = 0 ∨ ¬ squarefree d ∨ d > D) :
    selberg_lambda D d = 0 := by
  rw [selberg_lambda]
  simp only [h, if_true]

lemma lambda_defined (d : ℕ) (hpos : d ≠ 0) (hsq : squarefree d) (hle : d ≤ D) :
    selberg_lambda D d = (moebius d : ℝ) * Real.log (D / d) / Real.log D := by
  rw [selberg_lambda]
  simp only [hpos, hsq, Nat.not_lt.1 hle, not_false_eq_true, or_false, false_or, if_false]

lemma lambda_zero_if_large (d : ℕ) (h : d > D) :
    selberg_lambda D d = 0 :=
  lambda_vanishes D d (by simp [h, Nat.lt_irrefl])

lemma lambda_one : selberg_lambda D 1 = 1 := by
  have hsq : squarefree 1 := Nat.squarefree_one
  have hle : 1 ≤ D := Nat.one_le_of_lt hD
  have hlog : Real.log D ≠ 0 := (logD_pos D hD).ne'
  rw [lambda_defined D 1 (by decide) hsq hle]
  rw [moebius_one, Nat.div_self (by decide), Real.log_one]
  field_simp [hlog]
  exact one_div_one ▸ rfl

lemma lambda_support (d : ℕ) :
    selberg_lambda D d ≠ 0 → d ≠ 0 ∧ squarefree d ∧ d ≤ D := by
  contrapose!
  exact lambda_vanishes D d

end Selberg

end TwinPrimes
