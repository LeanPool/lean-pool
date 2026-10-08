/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.NormalizedDualToScaledNegOne
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CorrectorDecayRestrictionComposition

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.FixedGapNegOneRestriction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem originCube_outer_gap_three_volume_ratio
    {d : ℕ} (q : ℤ) :
    (volume (openCubeSet (originCube d (q + 3)))).toReal /
        (volume (openCubeSet (originCube d q))).toReal =
      ((3 : ℝ) ^ (3 : ℕ)) ^ d := by
  rw [volume_openCubeSet_toReal, volume_openCubeSet_toReal]
  rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale, ← div_pow]
  congr 1
  rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  change (3 : ℝ) ^ (q + 3 - q) = (3 : ℝ) ^ (3 : ℕ)
  rw [show q + 3 - q = (3 : ℤ) by omega]
  rfl

private theorem inverse_scale_gap_three (q : ℤ) :
    ((3 : ℝ) ^ q)⁻¹ =
      27 * ((3 : ℝ) ^ (q + 3))⁻¹ := by
  rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  norm_num
  have hq : (3 : ℝ) ^ q ≠ 0 := zpow_ne_zero q (by norm_num)
  field_simp [hq]

/-- The fixed three-generation restriction cost. -/
@[expose]
def gapThreeNegOneRestrictionConstant (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (27 * Real.sqrt (((3 : ℝ) ^ (3 : ℕ)) ^ d))

theorem gapThreeNegOneRestrictionConstant_lt_top (d : ℕ) :
    gapThreeNegOneRestrictionConstant d < ∞ := by
  exact ENNReal.ofReal_lt_top

/-- Restricting a local `L²` class across the fixed three-generation gap
costs a dimension-only factor after inverse-side-length normalization. -/
theorem triadicScaledNegOne_restrict_gap_three_le
    {d : ℕ} [NeZero d] (q : ℤ)
    (F : HilbertVectorL2 (openCubeSet (originCube d (q + 3)))) :
    let hsub : openCubeSet (originCube d q) ⊆
        openCubeSet (originCube d (q + 3)) :=
      openCubeSet_originCube_subset_of_le (by omega)
    triadicScaledNegOneNorm q (localHilbertVectorL2Restrict hsub F) ≤
      gapThreeNegOneRestrictionConstant d *
        triadicScaledNegOneNorm (q + 3) F := by
  dsimp only
  let U : Set (Vec d) := openCubeSet (originCube d q)
  let V : Set (Vec d) := openCubeSet (originCube d (q + 3))
  let hsub : U ⊆ V := openCubeSet_originCube_subset_of_le (by omega)
  have hU0 : volume U ≠ 0 := by
    exact (ENNReal.toReal_pos_iff.mp (by
      simpa only [U] using
        volume_openCubeSet_originCube_toReal_pos (d := d) q)).1.ne'
  have hUtop : volume U ≠ ∞ := by
    simpa only [U] using (volume_openCubeSet_lt_top (originCube d q)).ne
  have hV0 : volume V ≠ 0 := by
    exact (ENNReal.toReal_pos_iff.mp (by
      simpa only [V] using
        volume_openCubeSet_originCube_toReal_pos (d := d) (q + 3))).1.ne'
  have hVtop : volume V ≠ ∞ := by
    simpa only [V] using
      (volume_openCubeSet_lt_top (originCube d (q + 3))).ne
  have hrestrict := localNegOneNorm_restrict_le_sqrt_volumeRatio
    hsub hU0 hUtop hV0 hVtop F
  have hratio : (volume V).toReal / (volume U).toReal =
      ((3 : ℝ) ^ (3 : ℕ)) ^ d := by
    simpa only [U, V] using
      originCube_outer_gap_three_volume_ratio (d := d) q
  unfold triadicScaledNegOneNorm
  calc
    ENNReal.ofReal (((3 : ℝ) ^ q)⁻¹) *
          localNegOneNorm U (localHilbertVectorL2Restrict hsub F) ≤
        ENNReal.ofReal (((3 : ℝ) ^ q)⁻¹) *
          (ENNReal.ofReal
              (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
            localNegOneNorm V F) := mul_le_mul_right hrestrict _
    _ = gapThreeNegOneRestrictionConstant d *
          (ENNReal.ofReal (((3 : ℝ) ^ (q + 3))⁻¹) *
            localNegOneNorm V F) := by
      rw [hratio, inverse_scale_gap_three]
      unfold gapThreeNegOneRestrictionConstant
      rw [show ENNReal.ofReal
          (27 * ((3 : ℝ) ^ (q + 3))⁻¹) =
            ENNReal.ofReal 27 *
              ENNReal.ofReal (((3 : ℝ) ^ (q + 3))⁻¹) by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27)]]
      rw [show ENNReal.ofReal
          (27 * Real.sqrt (((3 : ℝ) ^ (3 : ℕ)) ^ d)) =
            ENNReal.ofReal 27 *
              ENNReal.ofReal
                (Real.sqrt (((3 : ℝ) ^ (3 : ℕ)) ^ d)) by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27)]]
      ac_rfl

end

end HighContrast
end HCPolySupport
