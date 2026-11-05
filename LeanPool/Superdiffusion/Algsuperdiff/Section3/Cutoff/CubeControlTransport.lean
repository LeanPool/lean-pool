/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Majorant
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Model
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.SubgaussianTail

/-!
# CubeControlTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Elementary transports for the local cube control

This module records the direct unit-cube consequences of J2 used by the later
finite-cover argument.  It deliberately does not assert an off-cube tail.
-/

namespace Algsuperdiff.Section3.Cutoff

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

theorem unitCubeValueNorm_le_j2Observable (j : ShellField d) :
    ShellField.unitCubeValueNorm j ≤ ShellField.j2Observable d j := by
  calc
    ShellField.unitCubeValueNorm j ≤
        ShellField.unitCubeValueNorm j + Real.sqrt d * ShellField.unitCubeDerivNorm j :=
      le_add_of_nonneg_right
        (mul_nonneg (Real.sqrt_nonneg _) (ShellField.unitCubeDerivNorm_nonneg j))
    _ ≤ ShellField.unitCubeValueNorm j + Real.sqrt d * ShellField.unitCubeDerivNorm j +
        (d : ℝ) * ShellField.unitCubeSecondDerivNorm j :=
      le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg d) (ShellField.unitCubeSecondDerivNorm_nonneg j))
    _ = ShellField.j2Observable d j := rfl

private theorem spatialScale_one (j : ShellField d) :
    ShellField.spatialScale 1 j = j := by
  apply Subtype.ext
  apply Prod.ext
  · apply ContinuousMap.ext
    intro x
    simp [ShellField.spatialScale_apply]
  · apply Prod.ext
    · apply ContinuousMap.ext
      intro x
      apply ContinuousLinearMap.ext
      intro v
      change ShellField.deriv (ShellField.spatialScale 1 j) x v =
        ShellField.deriv j x v
      rw [ShellField.spatialScale_deriv]
      simp
    · apply ContinuousMap.ext
      intro x
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change ShellField.secondDeriv (ShellField.spatialScale 1 j) x u v =
        ShellField.secondDeriv j x u v
      rw [ShellField.spatialScale_secondDeriv]
      simp

theorem localCubeControl_zero_eq_unitCubeValueNorm (j : ShellField d) :
    localCubeControl 0 j = ShellField.unitCubeValueNorm j := by
  unfold localCubeControl
  rw [cubeScaleFactor_originCube]
  norm_num
  rw [spatialScale_one]

/-- J2 supplies an integrable unit-cube value control for the zero shell. -/
theorem integrable_unitCubeValueNorm_zero (M : ABKModel d) :
    Integrable (fun omega : ShellSeq d => ShellField.unitCubeValueNorm (omega 0))
      M.P.toMeasure := by
  let X : ShellSeq d → ℝ := fun omega => ShellField.j2Observable d (omega 0)
  have hXmeas : Measurable X :=
    (ShellField.j2Observable_measurable d).comp ShellField.measurable_zeroShellMap
  have hXnonneg : ∀ omega, 0 ≤ X omega := fun omega =>
    ShellField.j2Observable_nonneg d (omega 0)
  have hX : MemLp X 2 M.P.toMeasure :=
    Algsuperdiff.Probability.memLp_two_of_gaussian_tail hXmeas hXnonneg M.J2.gaussian_tail
  apply (hX.integrable one_le_two).mono'
  · exact ((ShellField.unitCubeValueNorm_measurable).comp
      ShellField.measurable_zeroShellMap).aestronglyMeasurable
  · filter_upwards with omega
    change ‖ShellField.unitCubeValueNorm (omega 0)‖ ≤
      ShellField.j2Observable d (omega 0)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (ShellField.unitCubeValueNorm_nonneg (omega 0))]
    exact unitCubeValueNorm_le_j2Observable (omega 0)

end

end Algsuperdiff.Section3.Cutoff
