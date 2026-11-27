/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylIrreducibility

/-!
# Actual Gaussian Weyl averages after real linear relabeling

For every real continuous linear label map T, the Gaussian weighted strong
vector integral defines a bounded complex linear operator. Its vacuum
expectation is a genuinely integrable strictly positive real Gaussian,
so the averaged vacuum is nonzero. Symplecticity is not required for these
facts. Projection and intertwining identities require further proofs.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap
open scoped ComplexConjugate

variable {m : ℕ}

theorem integrable_relabeledWeylOrbit
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (x : MultiModeOscillatorSpace m) :
    Integrable (fun z : Fin m → ℂ =>
      weylVacuumWeight m z • multiOscillatorWeyl (T (WithLp.toLp 2 z)) x) := by
  have hc : Continuous (fun z : Fin m → ℂ =>
      weylVacuumWeight m z • multiOscillatorWeyl (T (WithLp.toLp 2 z)) x) := by
    have hW := (continuous_multiOscillatorWeyl_apply x).comp
      (T.continuous.comp (PiLp.continuous_toLp 2 _))
    have hw : Continuous (weylVacuumWeight m) := by unfold weylVacuumWeight; fun_prop
    exact hw.smul hW
  apply ((integrable_weylVacuumWeight m).norm.mul_const ‖x‖).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [norm_smul, norm_multiOscillatorWeyl_apply]

/-- Linear map for the relabeled Weyl average linear, of type `MultiModeOscillatorSpace m →ₗ[ℂ]
MultiModeOscillatorSpace m where toFun x`. -/
def relabeledWeylAverageLinear
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    MultiModeOscillatorSpace m →ₗ[ℂ] MultiModeOscillatorSpace m where
  toFun x := ∫ z : Fin m → ℂ,
    weylVacuumWeight m z • multiOscillatorWeyl (T (WithLp.toLp 2 z)) x
  map_add' x y := by
    simp only [map_add, smul_add]
    exact integral_add (integrable_relabeledWeylOrbit T x) (integrable_relabeledWeylOrbit T y)
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    simp_rw [smul_comm (weylVacuumWeight m _) c]
    exact integral_smul c _

theorem norm_relabeledWeylAverageLinear_le
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (x : MultiModeOscillatorSpace m) :
    ‖relabeledWeylAverageLinear T x‖ ≤
      (∫ z : Fin m → ℂ, ‖weylVacuumWeight m z‖) * ‖x‖ := by
  calc
    _ ≤ ∫ z : Fin m → ℂ,
        ‖weylVacuumWeight m z • multiOscillatorWeyl (T (WithLp.toLp 2 z)) x‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp only [norm_smul, norm_multiOscillatorWeyl_apply]
      exact integral_mul_const ‖x‖ _

/-- Continuous linear map for the relabeled Weyl average, of type `MultiModeOscillatorSpace m →L[ℂ]
MultiModeOscillatorSpace m`. -/
def relabeledWeylAverage
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  (relabeledWeylAverageLinear T).mkContinuous
    (∫ z : Fin m → ℂ, ‖weylVacuumWeight m z‖) (norm_relabeledWeylAverageLinear_le T)

@[simp] theorem relabeledWeylAverage_apply
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (x : MultiModeOscillatorSpace m) :
    relabeledWeylAverage T x = ∫ z : Fin m → ℂ,
      weylVacuumWeight m z • multiOscillatorWeyl (T (WithLp.toLp 2 z)) x := rfl

theorem inner_relabeledWeylAverage
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    inner ℂ x (relabeledWeylAverage T y) =
      ∫ z : Fin m → ℂ, weylVacuumWeight m z *
        inner ℂ x (multiOscillatorWeyl (T (WithLp.toLp 2 z)) y) := by
  rw [relabeledWeylAverage_apply, ← integral_inner (integrable_relabeledWeylOrbit T y)]
  simp only [inner_smul_right]

/-- Relabeled vacuum Gaussian defined as `Real.exp (-(‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^
2 + ‖T (WithLp.toLp 2 z)‖ ^ 2) / 2)`. -/
def relabeledVacuumGaussian
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) (z : Fin m → ℂ) : ℝ :=
  Real.exp (-(‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 +
    ‖T (WithLp.toLp 2 z)‖ ^ 2) / 2)

theorem relabeledWeylOrbit_vacuum_inner
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) (z : Fin m → ℂ) :
    inner ℂ (multiCoherentVector (0 : MultiModePhaseSpace m))
      (weylVacuumWeight m z •
        multiOscillatorWeyl (T (WithLp.toLp 2 z)) (multiCoherentVector 0)) =
      (relabeledVacuumGaussian T z : ℂ) := by
  rw [inner_smul_right, multiOscillatorWeyl_vacuum, weylVacuumWeight,
    relabeledVacuumGaussian, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem integrable_relabeledVacuumGaussian
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    Integrable (relabeledVacuumGaussian T) := by
  have hi := Integrable.const_inner (𝕜 := ℂ) (multiCoherentVector (0 : MultiModePhaseSpace m))
    (integrable_relabeledWeylOrbit T (multiCoherentVector 0))
  simp_rw [relabeledWeylOrbit_vacuum_inner] at hi
  simpa only [RCLike.re_to_complex, Complex.ofReal_re] using hi.re

theorem integral_relabeledVacuumGaussian_pos
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    0 < ∫ z : Fin m → ℂ, relabeledVacuumGaussian T z :=
  integral_exp_pos (integrable_relabeledVacuumGaussian T)

theorem inner_relabeledWeylAverage_vacuum
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    inner ℂ (multiCoherentVector (0 : MultiModePhaseSpace m))
      (relabeledWeylAverage T (multiCoherentVector 0)) =
      ((∫ z : Fin m → ℂ, relabeledVacuumGaussian T z : ℝ) : ℂ) := by
  rw [relabeledWeylAverage_apply,
    ← integral_inner (integrable_relabeledWeylOrbit T (multiCoherentVector 0))]
  simp_rw [relabeledWeylOrbit_vacuum_inner]
  exact integral_ofReal

/-- A concrete nonzero candidate vacuum for subsequent symplectic
projection identities. This theorem itself needs no symplectic premise. -/
theorem relabeledWeylAverage_vacuum_ne_zero
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) :
    relabeledWeylAverage T (multiCoherentVector (0 : MultiModePhaseSpace m)) ≠ 0 := by
  intro hz
  have h := inner_relabeledWeylAverage_vacuum T
  rw [hz, inner_zero_right] at h
  have hr : (∫ z : Fin m → ℂ, relabeledVacuumGaussian T z) = 0 := by
    exact Complex.ofReal_injective h.symm
  exact (ne_of_gt (integral_relabeledVacuumGaussian_pos T)) hr

end VacuumBellSeparation.Gaussian
