/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.GenerationSelection

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ClosedBallNearRatio

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The near-terminal ball comparison

The large-scale C¹ slope approximation's ball terminal necessarily has a band on
which
the cube row is silent: the canonical outer cube of `r` overshoots every
triadic cube contained in the ball of radius `R` as soon as
`108 * (√d * r) > R`, and — since `2 ≤ d` — that band always contains `r = R`.

On that band the only available comparison is ball against ball, with a
law-free volume ratio.  This module supplies it, in the same style as
`ClosedBallVolumeRatio`: the closed ball of radius `R` sits inside the open
ball of radius `216 √d · r`, whose volume is `(216 √d) ^ d` times the open ball
of radius `r`, which the closed ball of radius `r` contains.

Nothing here is an estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The closed balls are monotone in the radius. -/
theorem closedNormBall_mono {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    closedNormBall d r ⊆ closedNormBall d R := by
  intro y hy
  have hy' : vecNormSq y ≤ r ^ 2 := hy
  have hsq : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr hrR 2
  exact le_trans hy' hsq

/-- **The near-terminal ball volume ratio is law-free.** -/
theorem closedNormBall_volume_ratio_le_of_near [NeZero d] {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hnear : R < 108 * (Real.sqrt d * r)) :
    volume (closedNormBall d R) / volume (closedNormBall d r) ≤
      ENNReal.ofReal ((216 * Real.sqrt d) ^ d) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hfac : (0 : ℝ) < 216 * Real.sqrt d := by positivity
  have hsub : closedNormBall d R ⊆
      euclideanBall d (216 * Real.sqrt d * r) := by
    refine (closedNormBall_subset_euclideanBall_two_mul hR).trans ?_
    intro y hy
    have hy' : vecNormSq y < (2 * R) ^ 2 := (mem_euclideanBall_iff y).mp hy
    rw [mem_euclideanBall_iff]
    have hlt : 2 * R < 216 * Real.sqrt d * r := by
      linarith only [hnear]
    have h2R : (0 : ℝ) < 2 * R := by positivity
    exact lt_trans hy' (pow_lt_pow_left₀ hlt h2R.le (by norm_num))
  have hmono : volume (closedNormBall d R) ≤
      volume (euclideanBall d (216 * Real.sqrt d * r)) := measure_mono hsub
  have hdil : volume (euclideanBall d (216 * Real.sqrt d * r)) =
      ENNReal.ofReal ((216 * Real.sqrt d) ^ d) *
        volume (euclideanBall d r) :=
    volume_euclideanBall_const_mul hfac hr
  have hEB : volume (euclideanBall d r) ≤ volume (closedNormBall d r) :=
    measure_mono (euclideanBall_subset_closedNormBall d r)
  refine ENNReal.div_le_of_le_mul ?_
  calc volume (closedNormBall d R)
      ≤ ENNReal.ofReal ((216 * Real.sqrt d) ^ d) *
          volume (euclideanBall d r) := by rw [← hdil]; exact hmono
    _ ≤ ENNReal.ofReal ((216 * Real.sqrt d) ^ d) *
          volume (closedNormBall d r) := by gcongr

/-- **The near-terminal energy comparison.** -/
theorem weightedGradNorm_closedNormBall_le_of_near [NeZero d] {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hnear : R < 108 * (Real.sqrt d * r))
    (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b (closedNormBall d r) F ≤
      (ENNReal.ofReal ((216 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
        weightedGradNorm b (closedNormBall d R) F := by
  have hrestrict := weightedGradNorm_mono_set_le_volumeRatio
    (closedNormBall_mono (d := d) hr.le hrR)
    (volume_closedNormBall_ne_zero hr) (volume_closedNormBall_ne_top hr)
    (volume_closedNormBall_ne_zero hR) (volume_closedNormBall_ne_top hR) b F
  have hfactor : (volume (closedNormBall d R) /
        volume (closedNormBall d r)) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal ((216 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow
      (closedNormBall_volume_ratio_le_of_near hr hR hnear) (by norm_num)
  exact hrestrict.trans (mul_le_mul_left hfactor _)

end

end CorrectorComposition
end HighContrast
end HCPolySupport
