/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ClosedBallGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ClosedBallVolumeRatio

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the large-scale C¹ slope approximation clause (b2), second step: the two volume ratios are
law-free constants

`weightedGradNorm_mono_set_le_volumeRatio` pays `(volume V / volume U) ^ (1/2)`
for a domain change.  For (b2) that ratio must be bounded by a constant
depending on `d` alone — otherwise the decay `(r/R)^η` the cube row supplies
would be eaten by the geometry.  Both bounds are proved here, from ingredients:

* inner side, `outerTriadicGeneration_volume_ratio_lt_euclideanBall` at radius
  `2 r` plus the exact doubling `volume_euclideanBall_two_mul`, giving
  `(3√d)^d · 2^d = (6√d)^d`;
* outer side, `scaleMatchedEuclideanBall_volume_ratio_le` plus the exact
  dilation `volume_euclideanBall_eq_ofReal_pow_mul`, giving
  `6^d · (2√d)^d = (12√d)^d`.

Neither uses an estimate, a law, a sample or a scale: they are volumes of
explicit sets.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Inner side -/

/-- **The inner volume ratio is law-free.**  The canonical triadic cube
enclosing the closed ball of radius `r` has volume at most `(6√d)^d` times the
ball's. -/
theorem outerCube_closedNormBall_volume_ratio_le [NeZero d] {r : ℝ} (hr : 0 < r) :
    volume (openCubeSet (originCube d
          (outerTriadicGeneration (2 * (2 * r)) (by positivity)))) /
        volume (closedNormBall d r) ≤
      ENNReal.ofReal ((6 * Real.sqrt d) ^ d) := by
  set m : ℤ := outerTriadicGeneration (2 * (2 * r)) (by positivity) with hm
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hr2 : (0 : ℝ) < 2 * r := by positivity
  -- the real-valued ratio, at radius `2 r`
  have hratio := outerTriadicGeneration_volume_ratio_lt_euclideanBall
    (d := d) (r := 2 * r) hr2
  -- finiteness / nonvanishing
  have hE2zero := Root.volume_euclideanBall_ne_zero (d := d) hr2
  have hE2top := Root.volume_euclideanBall_ne_top (d := d) (2 * r)
  have hEzero := Root.volume_euclideanBall_ne_zero (d := d) hr
  have hEtop := Root.volume_euclideanBall_ne_top (d := d) r
  have hCtop := volume_openCubeSet_ne_top (originCube d m)
  have hE2pos : 0 < (volume (euclideanBall d (2 * r))).toReal :=
    ENNReal.toReal_pos hE2zero hE2top
  -- step 1: the real inequality
  have hreal1 : (volume (openCubeSet (originCube d m))).toReal ≤
      (3 * Real.sqrt d) ^ d * (volume (euclideanBall d (2 * r))).toReal := by
    have h := (div_lt_iff₀ hE2pos).mp hratio
    exact le_of_lt h
  -- step 2: the exact doubling
  have hdouble : volume (euclideanBall d (2 * r)) =
      ENNReal.ofReal ((2 : ℝ) ^ d) * volume (euclideanBall d r) :=
    Root.volume_euclideanBall_two_mul hr
  have hE2real : (volume (euclideanBall d (2 * r))).toReal =
      (2 : ℝ) ^ d * (volume (euclideanBall d r)).toReal := by
    rw [hdouble, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d)]
  have hreal2 : (volume (openCubeSet (originCube d m))).toReal ≤
      (6 * Real.sqrt d) ^ d * (volume (euclideanBall d r)).toReal := by
    have hconst : (3 * Real.sqrt d) ^ d * ((2 : ℝ) ^ d) = (6 * Real.sqrt d) ^ d := by
      rw [← mul_pow]
      ring_nf
    calc (volume (openCubeSet (originCube d m))).toReal
        ≤ (3 * Real.sqrt d) ^ d * (volume (euclideanBall d (2 * r))).toReal :=
          hreal1
      _ = (3 * Real.sqrt d) ^ d * ((2 : ℝ) ^ d) *
            (volume (euclideanBall d r)).toReal := by rw [hE2real]; ring
      _ = (6 * Real.sqrt d) ^ d * (volume (euclideanBall d r)).toReal := by
          rw [hconst]
  -- step 3: lift to `ℝ≥0∞`
  have hCE : volume (openCubeSet (originCube d m)) ≤
      ENNReal.ofReal ((6 * Real.sqrt d) ^ d) * volume (euclideanBall d r) := by
    have hlift : ENNReal.ofReal
          ((volume (openCubeSet (originCube d m))).toReal) ≤
        ENNReal.ofReal
          ((6 * Real.sqrt d) ^ d * (volume (euclideanBall d r)).toReal) :=
      ENNReal.ofReal_le_ofReal hreal2
    rw [ENNReal.ofReal_toReal hCtop,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (6 * Real.sqrt d) ^ d),
      ENNReal.ofReal_toReal hEtop] at hlift
    exact hlift
  -- step 4: the closed ball is at least as big as the open one
  have hEB : volume (euclideanBall d r) ≤ volume (closedNormBall d r) :=
    measure_mono (euclideanBall_subset_closedNormBall d r)
  refine ENNReal.div_le_of_le_mul ?_
  exact hCE.trans (by gcongr)

/-! ## Outer side -/

/-- The exact dilation of the ball volume by a positive factor. -/
theorem volume_euclideanBall_const_mul [NeZero d] {c x : ℝ} (hc : 0 < c)
    (hx : 0 < x) :
    volume (euclideanBall d (c * x)) =
      ENNReal.ofReal (c ^ d) * volume (euclideanBall d x) := by
  rw [Root.volume_euclideanBall_eq_ofReal_pow_mul (by positivity : 0 < c * x),
    Root.volume_euclideanBall_eq_ofReal_pow_mul hx, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c ^ d), ← mul_pow]

/-- **The outer volume ratio is law-free.**  If the scale-matched ball of the
triadic cube at generation `q` has radius between `R / 3` and `R`, the closed
ball of radius `R` has volume at most `(12√d)^d` times the cube's. -/
theorem closedNormBall_cube_volume_ratio_le [NeZero d] {R : ℝ} (q : ℕ)
    (hq : Real.sqrt d * (3 : ℝ) ^ q ≤ R)
    (hqmax : R < 3 * (Real.sqrt d * (3 : ℝ) ^ q)) :
    volume (closedNormBall d R) /
        volume (openCubeSet (originCube d (q : ℤ))) ≤
      ENNReal.ofReal ((12 * Real.sqrt d) ^ d) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hx : (0 : ℝ) < Real.sqrt d * (3 : ℝ) ^ q := by positivity
  have hR : 0 < R := lt_of_lt_of_le hx hq
  -- the closed ball sits in a ball of radius `6 * (√d 3^q)`
  have hsub : closedNormBall d R ⊆ euclideanBall d (6 * (Real.sqrt d * (3 : ℝ) ^ q)) := by
    refine (closedNormBall_subset_euclideanBall_two_mul hR).trans ?_
    intro y hy
    have hy' : vecNormSq y < (2 * R) ^ 2 := (mem_euclideanBall_iff y).mp hy
    rw [mem_euclideanBall_iff]
    have hlt : 2 * R < 6 * (Real.sqrt d * (3 : ℝ) ^ q) := by
      linarith only [hqmax]
    have h2R : (0 : ℝ) < 2 * R := by positivity
    have hsq : (2 * R) ^ 2 < (6 * (Real.sqrt d * (3 : ℝ) ^ q)) ^ 2 := by
      exact pow_lt_pow_left₀ hlt h2R.le (by norm_num)
    exact lt_trans hy' hsq
  have hmono : volume (closedNormBall d R) ≤
      volume (euclideanBall d (6 * (Real.sqrt d * (3 : ℝ) ^ q))) :=
    measure_mono hsub
  have hdil : volume (euclideanBall d (6 * (Real.sqrt d * (3 : ℝ) ^ q))) =
      ENNReal.ofReal ((6 : ℝ) ^ d) *
        volume (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)) :=
    volume_euclideanBall_const_mul (by norm_num) hx
  -- the scale-matched ratio
  have hratio := scaleMatchedEuclideanBall_volume_ratio_le (d := d) q
  refine ENNReal.div_le_of_le_mul ?_
  have hcube := volume_openCubeSet_ne_zero (originCube d (q : ℤ))
  have hcubetop := volume_openCubeSet_ne_top (originCube d (q : ℤ))
  have hball : volume (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)) ≤
      ENNReal.ofReal ((2 * Real.sqrt d) ^ d) *
        volume (openCubeSet (originCube d (q : ℤ))) :=
    (ENNReal.div_le_iff_le_mul (Or.inl hcube) (Or.inl hcubetop)).mp hratio
  calc volume (closedNormBall d R)
      ≤ ENNReal.ofReal ((6 : ℝ) ^ d) *
          volume (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)) := by
        rw [← hdil]; exact hmono
    _ ≤ ENNReal.ofReal ((6 : ℝ) ^ d) *
          (ENNReal.ofReal ((2 * Real.sqrt d) ^ d) *
            volume (openCubeSet (originCube d (q : ℤ)))) := by
        gcongr
    _ = ENNReal.ofReal ((12 * Real.sqrt d) ^ d) *
          volume (openCubeSet (originCube d (q : ℤ))) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (6 : ℝ) ^ d),
          ← mul_pow]
        ring_nf

end

end CorrectorComposition
end HighContrast
end HCPolySupport
