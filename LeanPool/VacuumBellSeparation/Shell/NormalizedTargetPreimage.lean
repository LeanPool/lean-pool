/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.CanonicalShellPreimage

/-!
# An actual controlled Lorentz preimage of every normalized target

The map and momentum are explicit constructions from the real and
imaginary parts. Both genuine Euclidean operator norms and the energy
are strictly below 32/sin(theta). The transverse momentum is positive,
including at mass zero, so the manuscript's fold is avoided.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Normalized target momentum defined as `canonicalShellMomentum t (negativeMinkowskiLength
(complexSpacetimeRe z)) θ`. -/
noncomputable def normalizedTargetMomentum (t : ℝ) (z : ComplexSpacetime) (θ : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  canonicalShellMomentum t (negativeMinkowskiLength (complexSpacetimeRe z)) θ

/-- Normalized target preimage map of type `Spacetime ≃L[ℝ] Spacetime`. -/
noncomputable def normalizedTargetPreimageMap {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    Spacetime ≃L[ℝ] Spacetime :=
  lorentzNegativePairMatch
    (canonicalShellReal_negative
      (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)) hθ)
    (canonicalShellImaginary_negative
      (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)) hθ)
    (canonicalShellPair_orthogonal t (negativeMinkowskiLength (complexSpacetimeRe z)) θ)
    (normalizedTarget_real_negative hz) (normalizedTarget_imaginary_negative hz)
    (normalizedTarget_pair_orthogonal hz)

theorem normalizedTargetPreimageMap_isProper {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    IsProperLorentzMap (normalizedTargetPreimageMap hz hθ) :=
  lorentzNegativePairMatch_isProper _ _ _ _ _ _

theorem normalizedTargetPreimageMap_isOrthochronous {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    IsOrthochronousMap (normalizedTargetPreimageMap hz hθ) :=
  lorentzNegativePairMatch_isOrthochronous _ _ _ _ _ _

theorem normalizedTargetPreimageMap_boost {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    complexifiedSpacetimeMap (normalizedTargetPreimageMap hz hθ)
      (complexShellBoost t ((θ : ℂ) * Complex.I) (normalizedTargetMomentum t z θ)) = z := by
  let ρ := negativeMinkowskiLength (complexSpacetimeRe z)
  have hρ : 0 < ρ := negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)
  have hr : minkowskiForm (canonicalShellReal t ρ θ) (canonicalShellReal t ρ θ) =
      minkowskiForm (complexSpacetimeRe z) (complexSpacetimeRe z) := by
    rw [canonicalShellReal_square hρ hθ]
    dsimp only [ρ]
    rw [negativeMinkowskiLength_sq (normalizedTarget_real_negative hz), neg_neg]
  have hi : minkowskiForm (canonicalShellImaginary t ρ θ) (canonicalShellImaginary t ρ θ) =
      minkowskiForm (complexSpacetimeIm z) (complexSpacetimeIm z) := by
    rw [canonicalShellImaginary_square hθ]
    have hs := negativeMinkowskiLength_sq (normalizedTarget_real_negative hz)
    change ρ ^ 2 = _ at hs
    have hp := (complexShell_real_imaginary_pair hz.2.2.1).1
    linarith
  change complexifiedSpacetimeMap _ (complexShellBoost t ((θ : ℂ) * Complex.I)
    (canonicalShellMomentum t ρ θ)) = z
  rw [canonicalShellBoost_pair hρ hθ]
  exact (lorentzNegativePairMatch_complex _ _ _ _ _ _ hr hi).trans
    (complexSpacetime_re_add_im z)

theorem normalizedTargetMomentum_transverse_pos {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    0 < normalizedTargetMomentum t z θ 1 :=
  canonicalShellTransverse_pos (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)) hθ

theorem normalizedTargetMomentum_axis_coordinates (t : ℝ) (z : ComplexSpacetime) (θ : ℝ) :
    normalizedTargetMomentum t z θ 0 = 0 ∧ normalizedTargetMomentum t z θ 2 = 0 := by
  simp [normalizedTargetMomentum, canonicalShellMomentum]

theorem normalizedTargetMomentum_energy_pos {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    0 < dispersion t (normalizedTargetMomentum t z θ) := by
  rw [normalizedTargetMomentum, canonicalShellMomentum_dispersion
    (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)) hθ]
  exact canonicalShellEnergy_pos
    (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)) hθ

theorem normalizedTargetMomentum_energy_lt {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    dispersion t (normalizedTargetMomentum t z θ) < 32 / Real.sin θ := by
  rw [normalizedTargetMomentum, canonicalShellMomentum_dispersion
    (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)) hθ, canonicalShellEnergy]
  apply (div_lt_div_iff_of_pos_right hθ).2
  have hr := normalizedTarget_real_length_bounds hz
  have ht₀ : 0 ≤ t := hz.1
  have ht₁ : t ≤ 1 := hz.2.1
  have htsq : t ^ 2 ≤ 1 := by nlinarith
  have hrsq : negativeMinkowskiLength (complexSpacetimeRe z) ^ 2 ≤ 256 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.2)
      (show 0 ≤ 16 + negativeMinkowskiLength (complexSpacetimeRe z) by linarith)]
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg t)
    (sq_nonneg (negativeMinkowskiLength (complexSpacetimeRe z))))
  nlinarith [Real.sqrt_nonneg (t ^ 2 + negativeMinkowskiLength (complexSpacetimeRe z) ^ 2)]

theorem normalizedTargetPreimageMap_norm_bounds {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    spacetimeEuclideanOperatorNorm (normalizedTargetPreimageMap hz hθ) ≤ 24 / Real.sin θ ∧
      spacetimeEuclideanOperatorNorm (normalizedTargetPreimageMap hz hθ).symm ≤ 24 / Real.sin θ
        := by
  let ρ := negativeMinkowskiLength (complexSpacetimeRe z)
  have hρ : 0 < ρ := negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)
  let S := canonicalShellFrame (t := t) hρ hθ
  let T := normalizedTargetFrame hz
  have ht : (T (1, 0)).1 ≤ 3 := normalizedTargetFrame_gamma_le_three hz
  have hs : (S (1, 0)).1 * Real.sin θ ≤ 2 :=
    canonicalShellFrame_gamma_mul_sin_le_two hz.1 hz.2.1
      (normalizedTarget_real_length_bounds hz).1 hθ
  have hsp : 0 ≤ (S (1, 0)).1 :=
    (lorentzNegativePairFrame_isOrthochronous _ _ _).le
  have hb : 4 * (T (1, 0)).1 * (S (1, 0)).1 ≤ 24 / Real.sin θ := by
    apply (le_div_iff₀ hθ).2
    have h := mul_le_mul ht hs (mul_nonneg hsp hθ.le) (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  constructor
  · exact (lorentzNegativePairMatch_norm_le _ _ _ _ _ _).trans hb
  · exact (lorentzNegativePairMatch_inverse_norm_le _ _ _ _ _ _).trans hb

theorem normalizedTargetPreimageMap_norm_lt {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    spacetimeEuclideanOperatorNorm (normalizedTargetPreimageMap hz hθ) < 32 / Real.sin θ ∧
      spacetimeEuclideanOperatorNorm (normalizedTargetPreimageMap hz hθ).symm < 32 / Real.sin θ
        := by
  have h := normalizedTargetPreimageMap_norm_bounds hz hθ
  have hstrict : 24 / Real.sin θ < 32 / Real.sin θ :=
    (div_lt_div_iff_of_pos_right hθ).2 (by norm_num)
  exact ⟨h.1.trans_lt hstrict, h.2.trans_lt hstrict⟩

/-- Literal regular reference preimages, with strict energy and inverse-norm
margins. The parameter set includes mass zero. -/
theorem normalizedTarget_exists_controlled_preimage {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ (p : EuclideanSpace ℝ (Fin 3)) (Λ : Spacetime ≃L[ℝ] Spacetime),
      IsProperLorentzMap Λ ∧ IsOrthochronousMap Λ ∧
      complexifiedSpacetimeMap Λ (complexShellBoost t ((θ : ℂ) * Complex.I) p) = z ∧
      p 0 = 0 ∧ 0 < p 1 ∧ p 2 = 0 ∧
      0 < dispersion t p ∧ dispersion t p < 32 / Real.sin θ ∧
      spacetimeEuclideanOperatorNorm Λ < 32 / Real.sin θ ∧
      spacetimeEuclideanOperatorNorm Λ.symm < 32 / Real.sin θ := by
  exact ⟨normalizedTargetMomentum t z θ, normalizedTargetPreimageMap hz hθ,
    normalizedTargetPreimageMap_isProper hz hθ,
    normalizedTargetPreimageMap_isOrthochronous hz hθ,
    normalizedTargetPreimageMap_boost hz hθ,
    (normalizedTargetMomentum_axis_coordinates t z θ).1,
    normalizedTargetMomentum_transverse_pos hz hθ,
    (normalizedTargetMomentum_axis_coordinates t z θ).2,
    normalizedTargetMomentum_energy_pos hz hθ, normalizedTargetMomentum_energy_lt hz hθ,
    (normalizedTargetPreimageMap_norm_lt hz hθ).1, (normalizedTargetPreimageMap_norm_lt hz hθ).2⟩

end VacuumBellSeparation
