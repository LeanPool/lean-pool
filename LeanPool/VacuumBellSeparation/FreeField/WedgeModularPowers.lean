/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgePolarResolvent
public import LeanPool.VacuumBellSeparation.FreeField.UnitaryResolventPowers
public import LeanPool.VacuumBellSeparation.FreeField.SourcePowerRangeWitness

/-!
# Original wedge source powers and the full physical exponential domain

The halfspace uses its proved injectivity, not a false boundedness premise.
The actual Gram-resolvent calculus is identified with the full rapidity
multiplier for 0≤c≤1. Every original completed source vector satisfies the
bounded Gram weight identity for 0≤c≤1/2.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m)

/-- Left wedge source power. -/
noncomputable def leftWedgeSourcePower (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    ComplexSourceHilbert hm (leftWedgeTimeZero 0) →ₗ.[ℂ]
      ComplexSourceHilbert hm (leftWedgeTimeZero 0) :=
  resolventPowerRatio (sourceModularResolvent hm (leftWedgeTimeZero 0))
    (sourceModularResolvent_nonneg hm (leftWedgeTimeZero 0))
    (leftWedgeSourceModularResolvent_injective hm) c hc hc1

theorem leftWedgeSourcePower_fourier {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitaryPartialTransport (leftWedgeSourceFourierUnitary hm)
      (leftWedgeSourcePower hm c hc hc1) = rapidityExponential c := by
  rw [leftWedgeSourcePower,
    unitaryPartialTransport_resolventPowerRatio (leftWedgeSourceFourierUnitary hm)
      _ (sourceModularResolvent_nonneg hm (leftWedgeTimeZero 0))
      (sourceModularResolvent_le_one hm (leftWedgeTimeZero 0))
      (leftWedgeSourceModularResolvent_injective hm)
      _ (exponentialResolvent_nonneg rapidityMeasure _ _)
      (exponentialResolvent_le_one rapidityMeasure _ _)
      (exponentialResolvent_injective rapidityMeasure _ _)
      (leftWedgeSourceFourier_resolvent hm) hc hc1,
    resolventPowerRatio_exponentialResolvent rapidityMeasure _ _ hc hc1]
  have he : (fun ξ => c * rapidityFrequencyExponent 1 ξ) = rapidityFrequencyExponent c := by
    ext ξ
    unfold rapidityFrequencyExponent
    ring
  simp only [he, rapidityExponential]

theorem leftWedgeSourcePower_graph_fourier {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (x y : ComplexSourceHilbert hm (leftWedgeTimeZero 0)) :
    (x, y) ∈ (leftWedgeSourcePower hm c hc hc1).graph ↔
      (leftWedgeSourceFourierUnitary hm x, leftWedgeSourceFourierUnitary hm y) ∈
        (rapidityExponential c).graph := by
  rw [← leftWedgeSourcePower_fourier hm hc hc1, unitaryPartialTransport_mem_graph,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]

theorem leftWedgeSourcePower_physical {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitaryPartialTransport (leftWedgeSourcePolarUnitary hm 0)
      (leftWedgeSourcePower hm c hc hc1) = physicalRapidityExponential hm c := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rcases p with ⟨x, y⟩
  rw [unitaryPartialTransport_mem_graph, physicalRapidityExponential_mem_graph_iff,
    leftWedgeSourcePower_graph_fourier hm hc hc1]
  simp only [leftWedgeSourceFourierUnitary, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem leftWedgeSourcePower_sqrt_graph {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (z : ComplexSourceHilbert hm (leftWedgeTimeZero 0)) :
    (sourceGramRoot hm (leftWedgeTimeZero 0) z,
      sourceModularWeight hm (leftWedgeTimeZero 0) c z) ∈
        (leftWedgeSourcePower hm c hc (by linarith)).graph := by
  rw [leftWedgeSourcePower, resolventPowerRatio, boundedRatio_mem_graph]
  exact sourceModularWeight_range_witness hm (leftWedgeTimeZero 0) hc hc2 z

/-- Whole-source equality in the actual maximal physical power graph. -/
theorem physicalRapidityExponential_source_graph {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (z : ComplexSourceHilbert hm (leftWedgeTimeZero 0)) :
    (complexSourceMap hm (leftWedgeTimeZero 0) z,
      leftWedgeSourcePolarUnitary hm 0 (sourceModularWeight hm (leftWedgeTimeZero 0) c z)) ∈
        (physicalRapidityExponential hm c).graph := by
  rw [← leftWedgeSourcePower_physical hm hc (by linarith), unitaryPartialTransport_mem_graph,
    ← leftWedgeSourcePolarUnitary_factorization hm 0 z,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
  exact leftWedgeSourcePower_sqrt_graph hm hc hc2 z

end VacuumBellSeparation
