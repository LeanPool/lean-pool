/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.Core
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Approximation
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Recovery sequences for sequential relaxation

At every finite point, the infimum defining a sequential relaxation admits a diagonal recovery
sequence. At a point where the relaxation is `⊤`, such a sequence need not exist: for example,
the concrete test type may be empty. A dense realization supplies the missing approximating
sequence and therefore gives recovery sequences at every point, including points of infinite
relaxed energy.

These conclusions use only the pseudometric structure and, for the all-points result, density of
the realization. They do not require a quadratic law, closability, or a Markov property.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy.PreEnergy


universe u

variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

/-- Every finite point of a sequential relaxation has a recovery sequence.

The proof chooses, for each precision, an approximating sequence whose `liminf` is nearly
minimal and then one sufficiently late concrete test from that sequence.
-/
theorem hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt {x : X}
    (hfinite : P.sequentialRelaxation.FiniteAt x) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by
  let metricError : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let energyError : ℕ → ENNReal := fun n ↦ ((n : NNReal) : ENNReal)⁻¹
  have metricError_pos : ∀ n, 0 < metricError n := by
    intro n
    dsimp [metricError]
    positivity
  have energyError_pos : ∀ n, 0 < energyError n := by
    intro n
    simp [energyError]
  have exists_test : ∀ n, ∃ f : P.Test,
      dist x (P.toAmbient f) < metricError n ∧
        (P.energy f : ENNReal) < P.sequentialRelaxation x + energyError n := by
    intro n
    have hrelaxed :
        P.sequentialRelaxation x < P.sequentialRelaxation x + energyError n :=
      ENNReal.lt_add_right hfinite (energyError_pos n).ne'
    simpa only [dist_comm] using
      P.exists_test_near_of_relaxation_lt hrelaxed (metricError_pos n)
  choose test htest_near htest_energy using exists_test
  have metricError_tendsto : Tendsto metricError atTop (𝓝 0) := by
    simpa [metricError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdist :
      Tendsto (fun n ↦ dist x (P.toAmbient (test n))) atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze tendsto_const_nhds metricError_tendsto
    · intro n
      exact dist_nonneg
    · intro n
      exact (htest_near n).le
  have htest_tendsto : Tendsto (fun n ↦ P.toAmbient (test n)) atTop (𝓝 x) :=
    tendsto_of_tendsto_of_dist tendsto_const_nhds hdist
  let approximation : P.ApproximatingSequence x := ⟨test, htest_tendsto⟩
  have energyError_tendsto : Tendsto energyError atTop (𝓝 0) := by
    simpa [energyError] using ENNReal.tendsto_inv_nat_nhds_zero
  have hupper_tendsto :
      Tendsto (fun n ↦ P.sequentialRelaxation x + energyError n) atTop
        (𝓝 (P.sequentialRelaxation x)) := by
    simpa using (tendsto_const_nhds.add energyError_tendsto)
  have hlower :
      P.sequentialRelaxation x ≤
        liminf (fun n ↦ (P.energy (test n) : ENNReal)) atTop :=
    P.sequentialRelaxation_le_sequenceEnergy approximation
  have hupper :
      limsup (fun n ↦ (P.energy (test n) : ENNReal)) atTop ≤
        P.sequentialRelaxation x := by
    refine (limsup_le_limsup (Eventually.of_forall fun n ↦ (htest_energy n).le)).trans_eq ?_
    exact hupper_tendsto.limsup_eq
  exact ⟨approximation, tendsto_of_le_liminf_of_limsup_le hlower hupper⟩

/-- At an infinite-energy point, density supplies an approximating sequence; its energy must
converge to `⊤` because the relaxed energy is the infimum of all sequence `liminf`s. -/
private theorem hasRecoverySequenceAt_sequentialRelaxation_of_eq_top {x : X}
    (hDense : P.DenseRealization) (htop : P.sequentialRelaxation x = ⊤) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by
  obtain ⟨approximation⟩ := hDense.nonempty_approximatingSequence x
  have hlower : ⊤ ≤ P.sequenceEnergy approximation := by
    simpa only [htop] using P.sequentialRelaxation_le_sequenceEnergy approximation
  have henergy :
      Tendsto (fun n ↦ (P.energy (approximation.1 n) : ENNReal)) atTop (𝓝 ⊤) :=
    tendsto_of_le_liminf_of_limsup_le hlower le_top
      (by isBoundedDefault) (by isBoundedDefault)
  refine ⟨approximation, ?_⟩
  simpa only [htop] using henergy

/-- A dense concrete realization gives a recovery sequence for the sequential relaxation at
every ambient point.

Density is genuinely needed for the `⊤` branch: with an empty test type there is no
approximating sequence at all, while the defining infimum of the relaxation is still `⊤`.
-/
theorem hasRecoverySequenceAt_sequentialRelaxation
    (hDense : P.DenseRealization) (x : X) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by
  by_cases hfinite : P.sequentialRelaxation.FiniteAt x
  · exact P.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt hfinite
  · have htop : P.sequentialRelaxation x = ⊤ := by
      change ¬ P.sequentialRelaxation x ≠ ⊤ at hfinite
      exact not_ne_iff.mp hfinite
    exact P.hasRecoverySequenceAt_sequentialRelaxation_of_eq_top hDense htop

end FunctionalInequalities.Energy.PreEnergy
