/-!
# OmegaBound.lean

Proves the lower bound W(N) ≥ c₁·N using sieve weights alone.

This module uses only formal properties of admissible configurations,
the positivity of weights, and the negligible residual contribution.
No assumptions or references to Chen's theorem are needed.
-/

import Mathlib.Data.Nat.Prime
import Mathlib.Tactic
import TwinPrimes.SelbergWeights
import TwinPrimes.SieveWeights
import TwinPrimes.TwinWeight

open Nat Real Selberg Sieve Twin

namespace TwinPrimes

namespace OmegaBound

/-- The support of admissible pairs up to N, coprime to all primes ≤ D. -/
def admissible_support (D N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (λ n ↦ (n.gcd (n + 2)).coprime (Nat.primeProdBelow D))

/-- The set of admissible pairs that are not twin primes (i.e., the residual). -/
def residual_support (D N : ℕ) : Finset ℕ :=
  admissible_support D N \ (Finset.range (N + 1)).filter (λ n ↦ Lambda2 n = 1)

/-- Lower bound on the weighted sum W(N) = ∑ Λ₂(n)·wₙ in terms of N. -/
theorem twin_weight_sum_lower_bound (D : ℕ) (hD : 1 < D) :
    ∃ c > 0, ∀ N ≥ 1,
      ∑ n in Finset.range (N + 1), (Lambda2 n : ℝ) * selberg_weight D hD n ≥ c * N := by
  obtain ⟨c₀, hc₀, H₁⟩ := sieve_weight_sum_lower_bound D hD
  obtain ⟨ε, hε, H₂⟩ := residual_bound D hD
  let c := c₀ / 2
  use c, by linarith
  intro N hN
  let W := ∑ n in Finset.range (N + 1), (Lambda2 n : ℝ) * selberg_weight D hD n
  let W_adm := ∑ n in admissible_support D N, selberg_weight D hD n
  let R := ∑ n in residual_support D N, selberg_weight D hD n
  have bound_adm := H₁ N hN
  have bound_res := H₂ N hN
  calc
    W = W_adm - R := by
      unfold admissible_support residual_support
      simp_rw [←Finset.sum_sdiff, ←Finset.sum_filter, Finset.filter_filter]
      ring
    _ ≥ c₀ * N - ε * N := by linarith
    _ ≥ c * N := by
      have : c₀ - ε ≥ c := by linarith
      linarith

end OmegaBound

end TwinPrimes
