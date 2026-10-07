/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatBound
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffFull

/-!
# Bounds for the short-time cutoff

The three factors of the smooth cutoff lie between zero and one.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The extended normal-phase cutoff takes values in the unit interval. -/
theorem buShortEtaExt_bounds (scale : ℝ) (q : Vec3 × ℝ) :
    0 ≤ buShortEtaExt scale q ∧ buShortEtaExt scale q ≤ 1 := by
  have hnormal : 0 ≤ buShortNormalCutoff scale (q.1 2) ∧
      buShortNormalCutoff scale (q.1 2) ≤ 1 := by
    unfold buShortNormalCutoff
    exact ⟨smoothTransitionProfile.nonneg _, smoothTransitionProfile.le_one _⟩
  have hphase : 0 ≤ buShortPhaseCutoff
      ((buShortFExt (q.1 2) q.2 - buShortB scale) / buShortB scale) ∧
      buShortPhaseCutoff
        ((buShortFExt (q.1 2) q.2 - buShortB scale) / buShortB scale) ≤ 1 := by
    unfold buShortPhaseCutoff
    exact ⟨smoothTransitionProfile.nonneg _, smoothTransitionProfile.le_one _⟩
  constructor
  · exact mul_nonneg hnormal.1 hphase.1
  · exact (mul_le_mul_of_nonneg_right hnormal.2 hphase.1).trans
      (by simpa using hphase.2)

/-- The full compact cutoff takes values in the unit interval. -/
theorem buShortFullCutoff_bounds (scale R : ℝ) (hR : 0 < R)
    (ε : ℝ) (q : Vec3 × ℝ) :
    0 ≤ buShortFullCutoff scale R hR ε q ∧
      buShortFullCutoff scale R hR ε q ≤ 1 := by
  have hχ := ucSpatialCutoff_bounds (show 0 < 2 * R by positivity) q.1
  have hη := buShortEtaExt_bounds scale q
  have hθ := ucInitialTimeCutoff_bounds ε (q.2 - 1 / 2)
  change 0 ≤ _ * _ * _ ∧ _ * _ * _ ≤ 1
  constructor
  · exact mul_nonneg (mul_nonneg hχ.1 hη.1) hθ.1
  · have hχη : ucSpatialCutoff (2 * R) (by positivity) q.1 *
        buShortEtaExt scale q ≤ 1 :=
      (mul_le_mul_of_nonneg_right hχ.2 hη.1).trans
        (by simpa using hη.2)
    exact (mul_le_mul_of_nonneg_right hχη hθ.1).trans
      (by simpa using hθ.2)

/-- The sum of the three absolute spatial derivatives is a pointwise
bound for each individual derivative. -/
theorem buCut_spatialPartial_abs_le_sum
    (κ : Vec3 × ℝ → ℝ) (z : ParabolicPoint) (j : Fin 3) :
    |spatialPartial (buCutScalar κ) j z| ≤
      ∑ k : Fin 3, |spatialPartial (buCutScalar κ) k z| := by
  exact Finset.single_le_sum
    (f := fun k : Fin 3 => |spatialPartial (buCutScalar κ) k z|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ j)

end ESS
