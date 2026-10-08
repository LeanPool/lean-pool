/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Bridge.ComparisonMatrixRows
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormMaximum
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRecentCellLp
public import LeanPool.HighContrastHomogenization.Provider.Window.ScaleMeasurability
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# High-contrast homogenization: Provider.Response.ProfileMaximumLp

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Moments of the complete terminal maximum

The below-start maximum is rewritten over the countable aligned labels before
measurability is proved.  Minkowski then compares the complete history with
the centered history and source moment, without an independence assumption.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The scalar size of one adapted response against a positive reference is an
almost-everywhere measurable statistic. -/
theorem aemeasurable_blockSize_adaptedResponse
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    AEMeasurable (fun a => blockSize (adaptedResponse q k w a) F) P := by
  have hU := Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w
  have hvol : 0 < (volume (adaptedCellAt q k w)).toReal := by
    exact ENNReal.toReal_pos (Recurrence.volume_adaptedCellAt_pos hq k w).ne'
      hU.volume_lt_top.ne
  exact (Window.measurable_blockSize_coarseBlock hU.isOpen
    hU.isBoundedDomain hvol hF hFpd).aemeasurable

/-- One weighted source-excess term is almost-everywhere measurable. -/
theorem aemeasurable_source_excess_term
    {P : Measure (CoeffSpace d)} {rhoMax : ℝ} {q : Mat d} (hq : q.PosDef)
    (t k : ℤ) (w : Fin d → ℤ) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    AEMeasurable (fun a => ENNReal.ofReal
      ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
        blockExcess (adaptedResponse q k w a) F)) P := by
  have hsize := aemeasurable_blockSize_adaptedResponse (P := P) hq k w hF hFpd
  have hexc : AEMeasurable
      (fun a => blockExcess (adaptedResponse q k w a) F) P := by
    have hfun : (fun a => blockExcess (adaptedResponse q k w a) F) =
        fun a => max (blockSize (adaptedResponse q k w a) F - 1) 0 := by
      funext a
      have hA := Recurrence.isSymmetricBlockMat_adaptedResponse q k w a
      have hApsd := (posDef_toFullBlockMat hA
        (Recurrence.blockPosDef_adaptedResponse hq k w a)).posSemidef
      rw [blockExcess_eq hA hF hFpd hApsd,
        blockSize_eq_relSize hA hF hFpd hApsd]
    rw [hfun]
    exact (hsize.sub aemeasurable_const).max aemeasurable_const
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (hexc.const_mul ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ)))))

/-- The `L^Q` seminorm of the complete maximum is the `Q`-th root of its
defining history. -/
theorem eLpNorm_profileTotalMaximum_eq
    {P : Measure (CoeffSpace d)} {Q rhoMax : ℝ} (hQ : 0 < Q)
    (q : Mat d) (jStar t : ℤ) (F : BlockMat d)
    (hW : AEMeasurable (profileTotalMaximum P rhoMax q jStar t F) P) :
    eLpNorm (profileTotalMaximum P rhoMax q jStar t F)
        (ENNReal.ofReal Q) P =
      profileTotalHistory P Q rhoMax q jStar t F ^ Q⁻¹ := by
  have hp0 : ENNReal.ofReal Q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hQ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
      hW.aestronglyMeasurable,
    ENNReal.toReal_ofReal hQ.le, one_div]
  simp only [enorm_eq_self]
  rfl

end

end HCPolySupport.HighContrast.Response
