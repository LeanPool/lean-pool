/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.AxisCube
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorRealRadiusGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Real-radius centered-cube geometry

This module compares a centered Euclidean cube of arbitrary positive side
length with its canonical enclosing origin-centered triadic cube.  The
enclosing generation is the integer ceiling of the base-three logarithm, so
the construction uses no selected cube or fallback branch.

## Main definitions

* `centeredOpenCube`: the centered open axis cube of the given side length.
* `outerTriadicGeneration`: the canonical enclosing triadic generation.

## Main results

* `le_outerTriadicGeneration_scale` and its strict companion: the sharp
  ceiling bounds.
* `outerTriadicGeneration_scale_lt_three_mul`: the factor-three rounding
  bound.
* `centeredOpenCube_subset_openCubeSet_originCube_outerTriadicGeneration`:
  the exact centered-cube inclusion.
* `outerTriadicGeneration_volume_ratio_lt_euclideanBall`: the strict
  dimensional volume ratio bound.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

/-- The centered open axis cube of side length `R`. -/
@[expose]
def centeredOpenCube (d : ℕ) (R : ℝ) : Set (Vec d) :=
  axisCube (fun _ => -R / 2) R

/-- The canonical origin-cube generation enclosing a positive real side
length.  The positivity proof is retained in the interface and does not
affect the value. -/
@[expose]
def outerTriadicGeneration (R : ℝ) (_hR : 0 < R) : ℤ :=
  ⌈Real.logb 3 R⌉

/-- The real side length does not exceed its canonical enclosing triadic
scale. -/
theorem le_outerTriadicGeneration_scale {R : ℝ} (hR : 0 < R) :
    R ≤ (3 : ℝ) ^ outerTriadicGeneration R hR := by
  have hceil :
      Real.logb 3 R ≤ ((outerTriadicGeneration R hR : ℤ) : ℝ) := by
    rw [outerTriadicGeneration]
    exact Int.le_ceil _
  have hpow :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 3) hR).mp hceil
  simpa only [Real.rpow_intCast] using hpow

/-- The canonical enclosing triadic side loses strictly less than one factor
of three. -/
theorem outerTriadicGeneration_scale_lt_three_mul {R : ℝ} (hR : 0 < R) :
    (3 : ℝ) ^ outerTriadicGeneration R hR < 3 * R := by
  have hceil :
      ((outerTriadicGeneration R hR : ℤ) : ℝ) < Real.logb 3 R + 1 := by
    rw [outerTriadicGeneration]
    exact Int.ceil_lt_add_one _
  have hpow :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) hceil
  calc
    (3 : ℝ) ^ outerTriadicGeneration R hR =
        Real.rpow 3 ((outerTriadicGeneration R hR : ℤ) : ℝ) := by
      exact (Real.rpow_intCast 3 (outerTriadicGeneration R hR)).symm
    _ < Real.rpow 3 (Real.logb 3 R + 1) := hpow
    _ = R * 3 := by
      calc
        Real.rpow 3 (Real.logb 3 R + 1) =
            Real.rpow 3 (Real.logb 3 R) * Real.rpow 3 1 :=
          Real.rpow_add (by norm_num : (0 : ℝ) < 3) (Real.logb 3 R) 1
        _ = R * Real.rpow 3 1 := by
          exact congrArg (fun t : ℝ => t * Real.rpow 3 1)
            (Real.rpow_logb (by norm_num : (0 : ℝ) < 3)
              (by norm_num : (3 : ℝ) ≠ 1) hR)
        _ = R * 3 := by norm_num
    _ = 3 * R := by ring

/-- The centered real-side cube lies in the origin-centered triadic cube at
the canonical outer generation. -/
theorem centeredOpenCube_subset_openCubeSet_originCube_outerTriadicGeneration
    {d : ℕ} {R : ℝ} (hR : 0 < R) :
    centeredOpenCube d R ⊆
      openCubeSet (originCube d (outerTriadicGeneration R hR)) := by
  intro x hx
  have hx' : ∀ i : Fin d, -R / 2 < x i ∧ x i < -R / 2 + R := by
    simpa only [centeredOpenCube, axisCube, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Ioo] using hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  rcases hx' i with ⟨hlo, hhi⟩
  have hscale := le_outerTriadicGeneration_scale hR
  constructor <;> linarith only [hlo, hhi, hscale]

/-- The volume of a positive-side centered open cube is the side length to
the ambient dimension. -/
theorem volume_centeredOpenCube_toReal {d : ℕ} {R : ℝ} (hR : 0 < R) :
    (volume (centeredOpenCube d R)).toReal = R ^ d := by
  have hab :
      (fun _ : Fin d => -R / 2) ≤ (fun _ : Fin d => -R / 2 + R) := by
    intro i
    linarith only [hR]
  rw [centeredOpenCube, axisCube, Real.volume_pi_Ioo_toReal hab,
    show (fun i : Fin d => -R / 2 + R - -R / 2) =
      (fun _ : Fin d => R) from by
        funext i
        ring,
    Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]

end

end HighContrast
end HCPolySupport
