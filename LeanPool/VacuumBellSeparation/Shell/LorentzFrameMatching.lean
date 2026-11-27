/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.LorentzFrames
public import LeanPool.VacuumBellSeparation.FreeField.LorentzShellAction
public import LeanPool.VacuumBellSeparation.FreeField.ComplexLorentzForm
public import LeanPool.VacuumBellSeparation.FreeField.LorentzEuclideanBound
public import LeanPool.VacuumBellSeparation.FreeField.EuclideanSpacetimeComposition

/-!
# Matching two actual negative Minkowski pairs

The matching map is the target frame composed with the inverse source
frame. Properness, future orientation, both pair images and the genuine
Euclidean norm bounds are derived from these actual frames.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem IsProperLorentzMap.symm {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsProperLorentzMap Λ) : IsProperLorentzMap Λ.symm := by
  refine ⟨hΛ.1.symm, ?_⟩
  have h := Λ.toLinearEquiv.det_mul_det_symm
  simpa only [ContinuousLinearEquiv.toLinearEquiv_symm, hΛ.2, one_mul] using h

theorem IsProperLorentzMap.trans {Λ Γ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsProperLorentzMap Λ) (hΓ : IsProperLorentzMap Γ) :
    IsProperLorentzMap (Λ.trans Γ) := by
  refine ⟨hΛ.1.trans hΓ.1, ?_⟩
  change LinearMap.det (Γ.toLinearEquiv.toLinearMap.comp Λ.toLinearEquiv.toLinearMap) = 1
  rw [LinearMap.det_comp, hΛ.2, hΓ.2, mul_one]

theorem IsOrthochronousMap.trans {Λ Γ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ)
    (hfΛ : IsOrthochronousMap Λ) (hfΓ : IsOrthochronousMap Γ) :
    IsOrthochronousMap (Λ.trans Γ) := by
  have he : ((1, 0) : Spacetime) = onShell 1 0 := by simp [onShell, dispersion]
  change 0 < (Γ (Λ (1, 0))).1
  rw [he, lorentzMap_onShell 1 Λ hΛ hfΛ, lorentzMap_onShell 1 Γ hΓ hfΓ]
  exact dispersion_pos (by norm_num) _

/-- Continuous linear equivalence for the lorentz negative pair match, of type `Spacetime ≃L[ℝ]
Spacetime`. -/
noncomputable def lorentzNegativePairMatch {a b u v : Spacetime}
    (ha : minkowskiForm a a < 0) (hb : minkowskiForm b b < 0)
    (hab : minkowskiForm a b = 0)
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0) : Spacetime ≃L[ℝ] Spacetime :=
  (lorentzNegativePairFrame ha hb hab).symm.trans (lorentzNegativePairFrame hu hv huv)

section Matching

variable {a b u v : Spacetime}
    (ha : minkowskiForm a a < 0) (hb : minkowskiForm b b < 0)
    (hab : minkowskiForm a b = 0)
    (hu : minkowskiForm u u < 0) (hv : minkowskiForm v v < 0)
    (huv : minkowskiForm u v = 0)

theorem lorentzNegativePairMatch_isProper :
    IsProperLorentzMap (lorentzNegativePairMatch ha hb hab hu hv huv) :=
  (lorentzNegativePairFrame_isProper ha hb hab).symm.trans
    (lorentzNegativePairFrame_isProper hu hv huv)

theorem lorentzNegativePairMatch_isOrthochronous :
    IsOrthochronousMap (lorentzNegativePairMatch ha hb hab hu hv huv) :=
  IsOrthochronousMap.trans (lorentzNegativePairFrame_isProper ha hb hab).1.symm
    (lorentzNegativePairFrame_isProper hu hv huv).1
    (IsOrthochronousMap.symm (lorentzNegativePairFrame_isProper ha hb hab).1
      (lorentzNegativePairFrame_isOrthochronous ha hb hab))
    (lorentzNegativePairFrame_isOrthochronous hu hv huv)

theorem lorentzNegativePairMatch_first (hau : minkowskiForm a a = minkowskiForm u u) :
    lorentzNegativePairMatch ha hb hab hu hv huv a = u := by
  have hs : lorentzNegativePairFrame ha hb hab
      (negativeMinkowskiLength a • spacetimeAxis 0) = a := by
    rw [map_smul, lorentzNegativePairFrame_first, negativeMinkowskiLength_smul_unit ha]
  have hlen : negativeMinkowskiLength a = negativeMinkowskiLength u := by
    simp only [negativeMinkowskiLength, hau]
  have hinv : (lorentzNegativePairFrame ha hb hab).symm a =
      negativeMinkowskiLength a • spacetimeAxis 0 := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (congrArg (lorentzNegativePairFrame ha hb hab).symm hs).symm
  rw [lorentzNegativePairMatch, ContinuousLinearEquiv.trans_apply, hinv, hlen, map_smul,
    lorentzNegativePairFrame_first, negativeMinkowskiLength_smul_unit hu]

theorem lorentzNegativePairMatch_second (hbv : minkowskiForm b b = minkowskiForm v v) :
    lorentzNegativePairMatch ha hb hab hu hv huv b = v := by
  have hs : lorentzNegativePairFrame ha hb hab
      (negativeMinkowskiLength b • spacetimeAxis 1) = b := by
    rw [map_smul, lorentzNegativePairFrame_second, negativeMinkowskiLength_smul_unit hb]
  have hlen : negativeMinkowskiLength b = negativeMinkowskiLength v := by
    simp only [negativeMinkowskiLength, hbv]
  have hinv : (lorentzNegativePairFrame ha hb hab).symm b =
      negativeMinkowskiLength b • spacetimeAxis 1 := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (congrArg (lorentzNegativePairFrame ha hb hab).symm hs).symm
  rw [lorentzNegativePairMatch, ContinuousLinearEquiv.trans_apply, hinv, hlen, map_smul,
    lorentzNegativePairFrame_second, negativeMinkowskiLength_smul_unit hv]

theorem lorentzNegativePairMatch_complex (hau : minkowskiForm a a = minkowskiForm u u)
    (hbv : minkowskiForm b b = minkowskiForm v v) :
    complexifiedSpacetimeMap (lorentzNegativePairMatch ha hb hab hu hv huv)
        (complexSpacetimeOfReal a + Complex.I • complexSpacetimeOfReal b) =
      complexSpacetimeOfReal u + Complex.I • complexSpacetimeOfReal v := by
  rw [map_add, map_smul, complexifiedSpacetimeMap_ofReal, complexifiedSpacetimeMap_ofReal,
    lorentzNegativePairMatch_first ha hb hab hu hv huv hau,
    lorentzNegativePairMatch_second ha hb hab hu hv huv hbv]

theorem lorentzNegativePairMatch_norm_le :
    spacetimeEuclideanOperatorNorm (lorentzNegativePairMatch ha hb hab hu hv huv) ≤
      4 * (lorentzNegativePairFrame hu hv huv (1, 0)).1 *
        (lorentzNegativePairFrame ha hb hab (1, 0)).1 := by
  refine (spacetimeEuclideanOperatorNorm_trans_le _ _).trans ?_
  have ht := spacetimeEuclideanOperatorNorm_lorentz_le
    (lorentzNegativePairFrame_isProper hu hv huv).1
    (lorentzNegativePairFrame_isOrthochronous hu hv huv)
  have hs := spacetimeEuclideanOperatorNorm_lorentz_inverse_le
    (lorentzNegativePairFrame_isProper ha hb hab).1
    (lorentzNegativePairFrame_isOrthochronous ha hb hab)
  calc
    _ ≤ (2 * (lorentzNegativePairFrame hu hv huv (1, 0)).1) *
        (2 * (lorentzNegativePairFrame ha hb hab (1, 0)).1) :=
      mul_le_mul ht hs (spacetimeEuclideanOperatorNorm_nonneg _)
        (mul_nonneg (by norm_num) (lorentzNegativePairFrame_isOrthochronous hu hv huv).le)
    _ = _ := by ring

theorem lorentzNegativePairMatch_inverse_norm_le :
    spacetimeEuclideanOperatorNorm (lorentzNegativePairMatch ha hb hab hu hv huv).symm ≤
      4 * (lorentzNegativePairFrame hu hv huv (1, 0)).1 *
        (lorentzNegativePairFrame ha hb hab (1, 0)).1 := by
  change spacetimeEuclideanOperatorNorm
    ((lorentzNegativePairFrame hu hv huv).symm.trans (lorentzNegativePairFrame ha hb hab)) ≤ _
  simpa only [lorentzNegativePairMatch, mul_assoc, mul_left_comm, mul_comm] using
    lorentzNegativePairMatch_norm_le hu hv huv ha hb hab

end Matching

end VacuumBellSeparation
