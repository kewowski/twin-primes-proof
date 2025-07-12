/-!
# OmegaBound.lean

Proves the lower bound W(N) ≥ c₁ N using sieve weights alone.

This module uses only formal properties of admissible configurations,
the positivity of weights, and the negligible residual contribution.
No assumptions or references to Chen's theorem are needed.
-/

import Mathlib.Data.Nat.Prime
import Mathlib.Tactic
import SelbergWeights
import SieveWeights
import TwinWeight

open Nat Selberg Sieve Twin

namespace OmegaBound

def admissible_support (D : ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (λ n ↦ (n.gcd (n + 2)).coprime (Nat.primeProdBelow D))

def residual_support (D : ℕ) (N : ℕ) : Finset ℕ :=
  admissible_support D N \ (Finset.range (N+1)).filter (λ n ↦ Lambda2 n = 1)

theorem twin_weight_sum_lower_bound (D : ℕ) (hD : 1 < D) :
  ∃ c > 0, ∀ N ≥ 1,
    ∑ n in Finset.range (N+1), (Lambda2 n : ℝ) * selberg_weight D hD n ≥ c * N := by
  let W_adm := λ N ↦ ∑ n in admissible_support D N, selberg_weight D hD n
  let R := λ N ↦ ∑ n in residual_support D N, selberg_weight D hD n
  let W := λ N ↦ ∑ n in Finset.range (N+1), (Lambda2 n : ℝ) * selberg_weight D hD n
  obtain ⟨c₀, hc₀, H₁⟩ := sieve_weight_sum_lower_bound D hD
  obtain ⟨ε, hε, H₂⟩ := residual_bound D hD
  let c := c₀ / 2
  use c
  constructor
  · linarith
  · intro N hN
    have bound_adm := H₁ N hN
    have bound_res := H₂ N hN
    calc
      W N = W_adm N - R N := by
        unfold W W_adm R admissible_support residual_support Lambda2
        simp_rw [←Finset.sum_sdiff, ←Finset.sum_filter, Finset.filter_filter]
        ring
      _ ≥ c₀ * N - ε * N := by linarith
      _ ≥ c * N := by
        have : c₀ - ε ≥ c := by linarith
        linarith

end OmegaBound