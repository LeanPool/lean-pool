/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BicommutantSelfAdjoint

/-! # Nets from simultaneous finite-vector approximation -/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem exists_strong_net_of_finite_approximation (D : Set (H →L[ℂ] H))
    (T : H →L[ℂ] H)
    (happrox : ∀ s : Finset H, ∀ ε : ℝ, 0 < ε →
      ∃ A ∈ D, ∀ x ∈ s, ‖T x - A x‖ < ε) :
    ∃ As : (Finset H × ℕ) → (H →L[ℂ] H),
      (∀ i, As i ∈ D) ∧ ∀ x : H, Tendsto (fun i => As i x) atTop (𝓝 (T x)) := by
  classical
  have ha : ∀ i : Finset H × ℕ, ∃ A ∈ D,
      ∀ x ∈ i.1, ‖T x - A x‖ < 1 / ((i.2 : ℝ) + 1) := by
    intro i
    exact happrox i.1 _ (by positivity)
  choose As hmem hdist using ha
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

theorem exists_selfAdjoint_strong_approximation
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H))) (hsa : IsSelfAdjoint T) :
    ∃ As : (Finset H × ℕ) → (H →L[ℂ] H),
      (∀ i, As i ∈ S ∧ IsSelfAdjoint (As i)) ∧
        ∀ x : H, Tendsto (fun i => As i x) atTop (𝓝 (T x)) := by
  classical
  apply exists_strong_net_of_finite_approximation {A | A ∈ S ∧ IsSelfAdjoint A} T
  intro s ε hε
  obtain ⟨A, hA, hself, hdist⟩ := selfAdjoint_bicommutant_approximate_finite_family
    S hT hsa (fun x : s => (x : H)) hε
  exact ⟨A, ⟨hA, hself⟩, fun x hx => hdist ⟨x, hx⟩⟩

end VacuumBellSeparation
