/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Tilt.AdapterScalarization

/-!
# High-contrast homogenization: Provider.Quenched.Prop42Tilt.CorrectedTiltAdapter

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The native corrected tilt adapter

This is the reverse half of the adapted-to-Euclidean block adapter, scalarized
through the adapted hatted contrast.  Its scale and error coefficient are
exactly those supplied by the block theorem.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory Set

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- On the unit box for the absorbed adapter size and hatted trace gap, the
quadratic scalarization is bounded by the sharp convenient factor `9/2`. -/
theorem tilt_scalar_polynomial_le {eta x : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + eta) ^ 2 *
        (1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2) - 1 ≤
      (9 / 2 : ℝ) * (eta + x) := by
  have hetaSq : eta ^ 2 ≤ eta := by
    have hprod := mul_nonneg heta0 (sub_nonneg.mpr heta1)
    nlinarith only [hprod]
  have hxSq : x ^ 2 ≤ x := by
    have hprod := mul_nonneg hx0 (sub_nonneg.mpr hx1)
    nlinarith only [hprod]
  have hfirst : (1 + eta) ^ 2 ≤ 1 + 3 * eta := by
    nlinarith only [hetaSq]
  have hsecond :
      1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2 ≤
        1 + (3 / 2 : ℝ) * x := by
    nlinarith only [hxSq]
  have hleft0 : 0 ≤ (1 + eta) ^ 2 := sq_nonneg _
  have hright0 : 0 ≤ 1 + 3 * eta := by linarith only [heta0]
  have hfactor0 :
      0 ≤ 1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2 := by
    nlinarith only [hx0, sq_nonneg x]
  have hmul :
      (1 + eta) ^ 2 *
          (1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2) ≤
        (1 + 3 * eta) * (1 + (3 / 2 : ℝ) * x) := by
    calc
      (1 + eta) ^ 2 *
          (1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2) ≤
          (1 + 3 * eta) *
            (1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2) :=
        mul_le_mul_of_nonneg_right hfirst hfactor0
      _ ≤ (1 + 3 * eta) * (1 + (3 / 2 : ℝ) * x) :=
        mul_le_mul_of_nonneg_left hsecond hright0
  have hexEta : eta * x ≤ eta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 heta0
  have hexX : eta * x ≤ x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heta1 hx0
  have hcross : (9 / 2 : ℝ) * (eta * x) ≤
      (3 / 2 : ℝ) * eta + 3 * x := by
    nlinarith only [hexEta, hexX]
  nlinarith only [hmul, hcross]

/-- The form consumed by the corrected scalar transfer.  Once the native
adapter size and the dimension-rescaled hatted gap are at most one, the
Euclidean intrinsic contrast is the sum of a hatted term and an adapter term,
both with coefficient `9/2`. -/
theorem blockContrast_sub_one_le_tilt_sum_of_adapter [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {A E : BlockMat d} {l r : ℤ} {q : Mat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hEsymm : IsSymmetricBlockMat E) (hEpos : Book.Ch02.BlockPosDef E)
    (hq : IsRoundedGrid l q) (hfin : HasFiniteAdaptedMean P q r)
    {c : ℝ} (hc : 0 ≤ c)
    (hsub : BlockMatLoewnerLE
      (blockSub A (adaptedMean P q r)) (blockScale c E))
    (heta1 : c * blockSize E (adaptedMean P q r) ≤ 1)
    (hx1 : (d : ℝ) * (adaptedHattedContrast P q r - 1) ≤ 1) :
    blockContrast A - 1 ≤
      (9 / 2 : ℝ) * ((d : ℝ) * (adaptedHattedContrast P q r - 1)) +
        (9 / 2 : ℝ) * (c * blockSize E (adaptedMean P q r)) := by
  let eta : ℝ := c * blockSize E (adaptedMean P q r)
  let x : ℝ := (d : ℝ) * (adaptedHattedContrast P q r - 1)
  have hBsymm := Recurrence.isSymmetricBlockMat_adaptedMean P q r
  have hBpos := Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq r hfin
  have heta0 : 0 ≤ eta :=
    mul_nonneg hc (PortableHistory.blockSize_nonneg hEsymm hBsymm hBpos)
  have hhat1 := one_le_adaptedHattedContrast_of_rounded hq hfin
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg hd0 (sub_nonneg.mpr hhat1)
  have hpoly := blockContrast_sub_one_le_adaptedHatted_of_adapter
    hAsymm hApos hEsymm hEpos hq hfin hc hsub
  have habsorb := tilt_scalar_polynomial_le heta0
    (by simpa only [eta] using heta1) hx0 (by simpa only [x] using hx1)
  dsimp only [eta, x] at hpoly habsorb ⊢
  nlinarith only [hpoly, habsorb]

end

end Quenched
end HighContrast
end HCPolySupport
