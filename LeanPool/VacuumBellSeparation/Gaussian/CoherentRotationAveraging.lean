/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.TorusCoherentExpansion
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeWeylRepresentation
public import LeanPool.VacuumBellSeparation.Weyl.StrongContinuity
public import Mathlib.Analysis.Complex.Isometry

/-!
# Coherent continuity and actual rotation averaging

The constructed Weyl/coherent unitary transports genuine continuity of
kernel vectors. Coordinatewise complex rotations preserve actual
Lebesgue measure. Averaging a nonnegative measurable function over the
probability torus therefore leaves its integral unchanged, even when the
integral is infinite. This avoids an implicit polar-coordinate constant.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

/-- Measure-space instance for `UnitAddCircle`. -/
local instance coherentRotationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance coherentRotationProbabilityMeasure : IsProbabilityMeasure
  (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_multiCoherentVector (m : ℕ) : Continuous (multiCoherentVector (m := m)) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hv := tendsto_weylVec (id : MultiModePhaseSpace m → MultiModePhaseSpace m)
    (F := id) (F₀ := z) tendsto_id
  change Tendsto multiCoherentVector (𝓝 z) (𝓝 (multiCoherentVector z))
  simpa only [Function.comp_def, id_eq, multiWeylCoherentEquiv_weylVec] using
    (multiWeylCoherentEquiv m).continuous.continuousAt.tendsto.comp hv

theorem multiExponentialVector_eq_normalized {m : ℕ} (z : Fin m → ℂ) :
    multiExponentialVector z = Complex.exp ((‖WithLp.toLp 2 z‖ ^ 2 / 2 : ℝ) : ℂ) •
      multiCoherentVector (WithLp.toLp 2 z) := by
  rw [multiCoherentVector, smul_smul, ← Complex.exp_add]
  simp only [← Complex.ofReal_add, add_neg_cancel, Complex.ofReal_zero,
    Complex.exp_zero, one_smul]

theorem continuous_multiExponentialVector (m : ℕ) :
    Continuous (multiExponentialVector (m := m)) := by
  have h := (continuous_multiCoherentVector m).comp (PiLp.continuous_toLp 2 _)
  have hexp : Continuous (fun z : Fin m → ℂ =>
      Complex.exp ((‖WithLp.toLp 2 z‖ ^ 2 / 2 : ℝ) : ℂ)) := by fun_prop
  simpa only [Pi.smul_def', Function.comp_def, ← multiExponentialVector_eq_normalized] using
    hexp.smul h

/-- Torus coordinate rotation. -/
def torusCoordinateRotation {m : ℕ} (θ : UnitAddTorus (Fin m)) :
    (Fin m → ℂ) ≃ᵐ (Fin m → ℂ) :=
  MeasurableEquiv.piCongrRight fun j =>
    (rotation (AddCircle.toCircle (θ j))).toHomeomorph.toMeasurableEquiv

theorem torusCoordinateRotation_apply {m : ℕ} (θ : UnitAddTorus (Fin m)) (z : Fin m → ℂ) :
    torusCoordinateRotation θ z = torusCoherentLabel z θ := by
  funext j
  change rotation (AddCircle.toCircle (θ j)) (z j) = z j * fourier 1 (θ j)
  rw [rotation_apply, fourier_one, mul_comm]

theorem torusCoordinateRotation_measurePreserving {m : ℕ} (θ : UnitAddTorus (Fin m)) :
    MeasurePreserving (torusCoordinateRotation θ) :=
  volume_preserving_pi (fun j => (rotation (AddCircle.toCircle (θ j))).measurePreserving)

theorem continuous_torusCoherentLabel (m : ℕ) :
    Continuous (fun p : UnitAddTorus (Fin m) × (Fin m → ℂ) => torusCoherentLabel p.2 p.1) := by
  unfold torusCoherentLabel
  fun_prop

/-- Rotation averaging is an exact nonnegative-integral identity, with
the normalized torus measure and no finiteness premise. -/
theorem lintegral_eq_rotation_average {m : ℕ} (f : (Fin m → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : Fin m → ℂ, f z) =
      ∫⁻ z : Fin m → ℂ, ∫⁻ θ : UnitAddTorus (Fin m), f (torusCoherentLabel z θ) := by
  have hinv (θ : UnitAddTorus (Fin m)) :
      (∫⁻ z : Fin m → ℂ, f (torusCoherentLabel z θ)) = ∫⁻ z, f z := by
    simpa only [torusCoordinateRotation_apply] using
      (torusCoordinateRotation_measurePreserving θ).lintegral_comp_emb
        (torusCoordinateRotation θ).measurableEmbedding f
  calc
    _ = ∫⁻ θ : UnitAddTorus (Fin m), ∫⁻ z : Fin m → ℂ, f (torusCoherentLabel z θ) := by
      simp only [hinv, lintegral_const, measure_univ, mul_one]
    _ = _ := lintegral_lintegral_swap
      (hf.comp (continuous_torusCoherentLabel m).measurable).aemeasurable

end VacuumBellSeparation.Gaussian
