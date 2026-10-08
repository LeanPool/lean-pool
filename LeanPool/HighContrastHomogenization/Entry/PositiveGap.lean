/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.PositiveGap

/-!
# High-contrast homogenization: Entry.PositiveGap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The positive-gap lemma

Proves the real-exponent, almost-everywhere statement
near `l.fixed.geometry.positive.gap` by nonlinear interpolation, Young absorption,
and centering. All thirteen explicit binders of the statement are retained.
The dimension premise and redundant majorant positivity premise are unused;
an underscore prefix marks them and preserves their kinds, types and positions.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub blockTrace)
namespace HCPolySupport.HighContrast.Entry

open MeasureTheory Analysis
open scoped Matrix.Norms.L2Operator

/-- The printed positive-gap estimate with its exact coefficients. -/
theorem fixed_geometry_positive_gap
    (d : ℕ) (_hd : 2 ≤ d)
    (N : ℝ) (hN : 2 ≤ N)
    (P : Measure (CoeffSpace d)) (hP : IsProbabilityMeasure P)
    (F G : CoeffSpace d → BlockMat d)
    (hF : SchattenMemLp P N F) (hG : SchattenMemLp P N G)
    (hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a))
    (_hGpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (G a))
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    lqSchattenNorm P N
        (fun a => blockSub (F a)
          (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (F b) α β ∂P))) ≤
      (1 + (2 * (d : ℝ)) ^ N⁻¹) *
          lqSchattenNorm P N
            (fun a => blockSub (G a)
              (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (G b) α β ∂P))) +
        2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) *
            blockOpNorm
                (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (G b) α β ∂P)) ^
              (1 - N⁻¹) *
            blockTrace
                (blockSub (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (G b) α β ∂P))
                  (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (F b) α β ∂P))) ^
              N⁻¹ := by
  let : IsProbabilityMeasure P := hP
  have hN1 : 1 < N := (by norm_num : (1 : ℝ) < 2).trans_le hN
  have h := positiveGap_centered_bound hN1 hF hG hFpos hFG
  have hcoef : N / (N - 1) + (2 * (d : ℝ)) ^ (1 - N⁻¹) ≤
      2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) := by
    calc
      _ ≤ 2 + 2 * (d : ℝ) ^ (1 - N⁻¹) :=
        add_le_add (scalar_gap_absorption_factor_le_two hN)
          (scalar_gap_dimension_factor_le hN1.le (Nat.cast_nonneg d))
      _ = _ := by ring
  have htrace := (positiveGap_mean_gap_bounds hN1.le hF hG hFpos hFG).1
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _))
      (Real.rpow_nonneg htrace _)))

end HCPolySupport.HighContrast.Entry
