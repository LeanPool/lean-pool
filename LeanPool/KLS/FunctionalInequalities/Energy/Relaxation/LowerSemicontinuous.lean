/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Approximation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity of sequential relaxation

In a pseudometric ambient space, the sequential relaxation of every finite pre-energy is lower
semicontinuous. The proof is a diagonal argument: from points with uniformly bounded relaxed
energy, choose concrete tests that are simultaneously close to those points and whose energies
miss the bound by a vanishing error.

No quadratic law, dense-realization hypothesis, or Markov property is used here. Outside a
first-countable setting, a sequential relaxation need not describe the topological
lower-semicontinuous envelope.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy.PreEnergy

section Semicontinuity

universe u

variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

/-- Sequential relaxation is lower semicontinuous in a pseudometric ambient space. -/
theorem lowerSemicontinuous_sequentialRelaxation :
    LowerSemicontinuous (fun x ↦ P.sequentialRelaxation x) := by
  apply LowerSemicontinuous.of_frequently
  intro x bound hfrequent
  by_cases hbound : bound = ⊤
  · simp [hbound]
  obtain ⟨xseq, hxseq, hxseq_bound⟩ := exists_seq_forall_of_frequently hfrequent
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
      dist (P.toAmbient f) (xseq n) < metricError n ∧
        (P.energy f : ENNReal) < bound + energyError n := by
    intro n
    have hrelaxed : P.sequentialRelaxation (xseq n) < bound + energyError n :=
      (hxseq_bound n).trans_lt
        (ENNReal.lt_add_right hbound (energyError_pos n).ne')
    exact P.exists_test_near_of_relaxation_lt hrelaxed (metricError_pos n)
  choose test htest_near htest_energy using exists_test
  have metricError_tendsto : Tendsto metricError atTop (𝓝 0) := by
    simpa [metricError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdist :
      Tendsto (fun n ↦ dist (xseq n) (P.toAmbient (test n))) atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze tendsto_const_nhds metricError_tendsto
    · intro n
      exact dist_nonneg
    · intro n
      simpa [dist_comm] using (htest_near n).le
  have htest_tendsto : Tendsto (fun n ↦ P.toAmbient (test n)) atTop (𝓝 x) :=
    tendsto_of_tendsto_of_dist hxseq hdist
  let approximation : P.ApproximatingSequence x := ⟨test, htest_tendsto⟩
  have energyError_tendsto : Tendsto energyError atTop (𝓝 0) := by
    simpa [energyError] using ENNReal.tendsto_inv_nat_nhds_zero
  calc
    P.sequentialRelaxation x ≤ P.sequenceEnergy approximation :=
      P.sequentialRelaxation_le_sequenceEnergy approximation
    _ ≤ liminf (fun n ↦ bound + energyError n) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n ↦ (htest_energy n).le)
    _ = bound := by
      simpa using (tendsto_const_nhds.add energyError_tendsto).liminf_eq

end Semicontinuity

section Maximality

variable {X : Type*} [TopologicalSpace X] (P : PreEnergy X)

/-- A lower-semicontinuous functional bounded by the concrete test energies is bounded by
their sequential relaxation. No density or finite-energy agreement is required. -/
theorem le_sequentialRelaxation_of_lowerSemicontinuous
    (energy : Functional X) (hlsc : LowerSemicontinuous fun x ↦ energy x)
    (h : ∀ f : P.Test, energy (P.toAmbient f) ≤ (P.energy f : ENNReal)) (x : X) :
    energy x ≤ P.sequentialRelaxation x := by
  rw [P.sequentialRelaxation_apply]
  refine le_iInf fun s ↦ ?_
  have hlimit : energy x ≤ liminf (fun n ↦ energy (P.toAmbient (s.1 n))) atTop := by
    refine le_of_forall_lt fun c hc ↦ ?_
    obtain ⟨d, hcd, hd⟩ := exists_between hc
    have heventually := s.2.eventually (hlsc x d hd)
    exact hcd.trans_le (le_liminf_of_le (by isBoundedDefault)
      (heventually.mono fun _ hn ↦ hn.le))
  exact hlimit.trans (liminf_le_liminf (Eventually.of_forall fun n ↦ h (s.1 n)))

end Maximality

section Comparison

variable {X : Type*} [PseudoMetricSpace X] (P Q : PreEnergy X)

/-- Approximating each `P`-test by `Q`-tests at no greater limiting energy compares the two
relaxations. The hypothesis allows different test types and nonattained raw minima.

Both pre-energies use the same pseudometric ambient space, where the target relaxation is
lower semicontinuous. If each source test instead has a single exact target realization under
a continuous map, `PreEnergy.sequentialRelaxation_comp_le` applies even between different
topological spaces, without a pseudometric hypothesis.
-/
theorem sequentialRelaxation_le_of_recovery_sequences
    (h : ∀ f : P.Test, ∃ s : Q.ApproximatingSequence (P.toAmbient f),
      Q.sequenceEnergy s ≤ (P.energy f : ENNReal)) (x : X) :
    Q.sequentialRelaxation x ≤ P.sequentialRelaxation x := by
  apply P.le_sequentialRelaxation_of_lowerSemicontinuous Q.sequentialRelaxation
    Q.lowerSemicontinuous_sequentialRelaxation
  intro f
  obtain ⟨s, hs⟩ := h f
  exact (Q.sequentialRelaxation_le_sequenceEnergy s).trans hs

/-- Mutual approximation of concrete tests identifies their relaxed energies, including at
infinite-energy points. Applications must prove the two actual approximation hypotheses. -/
theorem sequentialRelaxation_eq_of_recovery_sequences
    (hPQ : ∀ f : P.Test, ∃ s : Q.ApproximatingSequence (P.toAmbient f),
      Q.sequenceEnergy s ≤ (P.energy f : ENNReal))
    (hQP : ∀ g : Q.Test, ∃ s : P.ApproximatingSequence (Q.toAmbient g),
      P.sequenceEnergy s ≤ (Q.energy g : ENNReal)) :
    P.sequentialRelaxation = Q.sequentialRelaxation := by
  ext x
  exact le_antisymm (Q.sequentialRelaxation_le_of_recovery_sequences P hQP x)
    (P.sequentialRelaxation_le_of_recovery_sequences Q hPQ x)

end Comparison

end FunctionalInequalities.Energy.PreEnergy
