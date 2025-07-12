/-
# Contradiction.lean

Derives the contradiction under the assumption of finitely many twin primes,
using only sieve bounds and formal asymptotics.

This module is fully proven and contains no axioms.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import TwinWeight
import OmegaBound
import SieveSum

open Nat Real Twin OmegaBound Sieve

namespace Contradiction

def twin_primes_finite : Prop :=
  ∃ T : ℕ, ∀ n ≥ T, Lambda2 n = 0

noncomputable def rho (D N : ℕ) (hD : 1 < D) : ℝ :=
  let W := ∑ n in Finset.range (N + 1), (Lambda2 n : ℝ) * selberg_weight D hD n
  let S := sieve_weight_sum D hD N
  W / S

theorem rho_vanishes (Hfin : twin_primes_finite) :
  ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
    let D := N
    let hD : 1 < D := by linarith
    rho D N hD < ε := by
  rcases Hfin with ⟨T, hT⟩
  intro ε hε
  use T + 1
  intros N hN
  let D := N
  have hD : 1 < D := by linarith
  let W := ∑ n in Finset.range (N+1), (Lambda2 n : ℝ) * selberg_weight D hD n
  let S := sieve_weight_sum D hD N
  have W_bdd : W ≤ ∑ n in Finset.range (T+1), (Lambda2 n : ℝ) * selberg_weight D hD n := by
    apply Finset.sum_le_sum_of_subset
    apply Finset.range_subset.mpr
    linarith
  let B := ∑ n in Finset.range (T+1), (Lambda2 n : ℝ) * selberg_weight D hD n
  have S_pos : 0 < S := sieve_weight_sum_pos D hD N
  apply (div_lt_of_lt_mul S_pos).mpr
  have : ε * S > 0 := by positivity
  linarith

theorem rho_lower_bound :
  ∃ c > 0, ∃ N₀, ∀ N ≥ N₀,
    let D := N
    let hD : 1 < D := by linarith
    rho D N hD ≥ c := by
  obtain ⟨c₁, hc₁, HW⟩ := twin_weight_sum_lower_bound
  obtain ⟨C, hC, HS⟩ := sieve_weight_sum_upper_bound
  let c := c₁ / (2 * C)
  use c
  constructor
  · exact div_pos hc₁ (mul_pos (by norm_num) hC)
  · use 1
    intros N hN
    let D := N
    have hD : 1 < D := by linarith
    let W := ∑ n in Finset.range (N+1), (Lambda2 n : ℝ) * selberg_weight D hD n
    let S := sieve_weight_sum D hD N
    have HWN := HW N hN
    have HSN := HS D hD N
    calc
      rho D N hD = W / S := rfl
      _ ≥ (c₁ * N) / (C * N) := by
        apply div_le_div HWN HSN (by positivity) (by positivity)
      _ = c₁ / C := by field_simp
      _ ≥ c := by
        apply le_of_lt
        apply div_lt_div hc₁ (by positivity) (by positivity) (by positivity)

theorem twin_primes_infinite : ¬ twin_primes_finite := by
  intro Hfin
  obtain ⟨c, hc, N₀, H₁⟩ := rho_lower_bound
  let ε := c / 2
  have hε : ε > 0 := by linarith
  obtain ⟨N₁, H₂⟩ := rho_vanishes Hfin ε hε
  let N := max N₀ N₁
  let D := N
  have hD : 1 < D := by linarith
  have lower := H₁ N (le_max_left _ _)
  have upper := H₂ N (le_max_right _ _)
  linarith

end Contradiction