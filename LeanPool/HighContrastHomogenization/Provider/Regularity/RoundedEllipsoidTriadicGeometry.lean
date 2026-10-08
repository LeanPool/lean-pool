/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusBallGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceConstantMatrix
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleDecay

/-!
# High-contrast homogenization: Provider.Regularity.RoundedEllipsoidTriadicGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded-coordinate ellipsoid and triadic endpoint geometry

The R3-A rounded map sends every physical adapted ellipsoid to the quadratic
sublevel set of the inverse rounded reference matrix.  The literal
`99/100`--`101/100` ellipticity window then gives dimension-only inner and
outer Euclidean comparisons.  These are the geometric endpoint facts used by
the Lane-C real-radius consumer.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The canonical rounded outer generation for a positive physical radius. -/
@[expose]
def roundedEllipsoidOuterGeneration (r : ℝ) (hr : 0 < r) : ℤ :=
  outerTriadicGeneration (4 * r) (by positivity)

/-- Canonical outer generations are monotone in their positive side length. -/
theorem outerTriadicGeneration_mono {R T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hRT : R ≤ T) :
    outerTriadicGeneration R hR ≤ outerTriadicGeneration T hT := by
  rw [outerTriadicGeneration, outerTriadicGeneration]
  exact Int.ceil_mono
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3) hR hRT)

/-- A deliberately interior terminal generation.  Its cube is uniformly
inside the rounded pullback at radius `R`; the factor `100*d` is geometric
slack only and is not inserted into the common effective scale. -/
@[expose]
def roundedEllipsoidTerminalGeneration [NeZero d]
    (R : ℝ) (hR : 0 < R) : ℤ :=
  outerTriadicGeneration (R / (100 * (d : ℝ))) (by
    have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
    positivity)

/-- In the small-radius branch, including its equality endpoint, the rounded
query generation does not exceed the interior terminal generation. -/
theorem roundedEllipsoidOuterGeneration_le_terminalGeneration
    [NeZero d] {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hsmall : r ≤ R / (400 * (d : ℝ))) :
    roundedEllipsoidOuterGeneration r hr ≤
      roundedEllipsoidTerminalGeneration (d := d) R hR := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  apply outerTriadicGeneration_mono (by positivity) (by positivity)
  calc
    4 * r ≤ 4 * (R / (400 * (d : ℝ))) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ = R / (100 * (d : ℝ)) := by field_simp; ring

/-- At the minimal admitted real radius, and hence at every later radius, the
rounded outer generation lies above the natural triadic ceiling of the common
scale. -/
theorem triadicCeilingIndex_cast_le_roundedEllipsoidOuterGeneration
    {x r : ℝ} (hx : 1 ≤ x) (hxr : x ≤ r) :
    (Quenched.triadicCeilingIndex x : ℤ) ≤
      roundedEllipsoidOuterGeneration r (zero_lt_one.trans_le (hx.trans hxr)) := by
  have hr : 0 < r := zero_lt_one.trans_le (hx.trans hxr)
  apply natCast_le_outerTriadicGeneration_of_pow_le (by positivity)
  have hceil := Quenched.pow_triadicCeilingIndex_le_three_mul hx
  calc
    (3 : ℝ) ^ Quenched.triadicCeilingIndex x ≤ 3 * x := hceil
    _ ≤ 3 * r := mul_le_mul_of_nonneg_left hxr (by norm_num)
    _ ≤ 4 * r := by nlinarith only [hr]

end

end HighContrast
end HCPolySupport
