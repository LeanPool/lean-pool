/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BicommutantFiniteApproximation

/-!
# Actual strong approximation nets in a unital star algebra

Finite subsets of the Hilbert space and increasing accuracy index a net
of algebra elements converging strongly to every double-commutant
operator. These approximants need not be norm bounded or selfadjoint.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_strong_approximation_in_starSubalgebra
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H))) :
    ∃ As : (Finset H × ℕ) → (H →L[ℂ] H),
      (∀ i, As i ∈ S) ∧ ∀ x : H, Tendsto (fun i => As i x) atTop (𝓝 (T x)) := by
  classical
  have happrox : ∀ i : Finset H × ℕ, ∃ A ∈ S,
      ∀ x ∈ i.1, ‖T x - A x‖ < 1 / ((i.2 : ℝ) + 1) := by
    intro i
    exact bicommutant_approximate_finset S hT i.1 (by positivity)
  choose As hmem hdist using happrox
  refine ⟨As, hmem, fun x => Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  apply eventually_atTop.mpr
  refine ⟨({x}, N), ?_⟩
  intro i hi
  have hxi : x ∈ i.1 := hi.1 (Finset.mem_singleton_self x)
  have hden : (N : ℝ) + 1 ≤ (i.2 : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hi.2 1
  have hbound : 1 / ((i.2 : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hden
  rw [dist_eq_norm, norm_sub_rev]
  exact (lt_of_lt_of_le (hdist i x hxi) hbound).trans hN

end VacuumBellSeparation
