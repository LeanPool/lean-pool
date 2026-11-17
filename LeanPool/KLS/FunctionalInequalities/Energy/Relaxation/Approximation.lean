/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Sequences

/-!
# Choosing concrete tests for sequential relaxation

Two elementary approximation steps are shared by the lower-semicontinuity and recovery proofs.
`exists_test_near_of_relaxation_lt` selects one test close to a prescribed point, with energy
below any strict upper bound for the relaxed energy.
`DenseRealization.nonempty_approximatingSequence`
supplies a convergent test sequence without imposing an energy bound.

The first step uses the definition of relaxation and the metric description of convergence.
The second uses Mathlib's `mem_closure_iff_seq_limit`. Neither step assumes quadraticity or
agreement of raw and relaxed energy. Keeping these choices here lets the consuming proofs focus
on their different conclusions: lower semicontinuity and convergence of recovery energies.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy.PreEnergy

universe u

variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

/-- A strict relaxed-energy bound can be realized by a concrete test in any positive-radius
neighborhood. The strict inequality is essential: an optimal test need not exist. -/
theorem exists_test_near_of_relaxation_lt {x : X} {bound : ENNReal}
    (hbound : P.sequentialRelaxation x < bound) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : P.Test, dist (P.toAmbient f) x < ε ∧ (P.energy f : ENNReal) < bound := by
  rw [P.sequentialRelaxation_apply, iInf_lt_iff] at hbound
  obtain ⟨approximation, henergy⟩ := hbound
  have hnear : ∀ᶠ k : ℕ in atTop,
      dist (P.toAmbient (approximation.1 k)) x < ε := by
    have htendsto := approximation.2
    rw [Metric.tendsto_atTop] at htendsto
    obtain ⟨N, hN⟩ := htendsto ε hε
    exact eventually_atTop.2 ⟨N, hN⟩
  have hlow : ∃ᶠ k : ℕ in atTop, (P.energy (approximation.1 k) : ENNReal) < bound :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) henergy
  obtain ⟨k, hk_energy, hk_near⟩ := (hlow.and_eventually hnear).exists
  exact ⟨approximation.1 k, hk_near, hk_energy⟩

/-- Dense realization supplies an approximating sequence at every point, including points where
the relaxed energy is infinite. It does not by itself give convergence of the energies. -/
theorem DenseRealization.nonempty_approximatingSequence {P : PreEnergy X}
    (hDense : P.DenseRealization) (x : X) :
    Nonempty (P.ApproximatingSequence x) := by
  obtain ⟨points, hpoints, htendsto⟩ := mem_closure_iff_seq_limit.mp (hDense x)
  choose tests htests using hpoints
  exact ⟨⟨tests, by simpa only [htests] using htendsto⟩⟩

end FunctionalInequalities.Energy.PreEnergy
