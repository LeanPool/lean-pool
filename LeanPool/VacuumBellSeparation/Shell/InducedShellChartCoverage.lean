/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeCompatibility
public import LeanPool.VacuumBellSeparation.Shell.NormalizedTargetPreimage

/-!
# Coverage of the literal normalized target by the regular volume charts

The positive transverse canonical momentum fixes the principal-root
branch. The explicit controlled matching map therefore places every
normalized target in one of the actual regular Lorentz shell charts.
This supplies coverage without an additional atlas-existence premise.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem canonicalShellBoost_second_coordinate (t ρ θ : ℝ) :
    (complexShellBoost t ((θ : ℂ) * Complex.I) (canonicalShellMomentum t ρ θ)).2 1 =
      (canonicalShellTransverse t ρ θ : ℂ) := rfl

theorem canonicalShellBoost_coordinates_mem_domain {t ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    complexShellCoordinates
      (complexShellBoost t ((θ : ℂ) * Complex.I) (canonicalShellMomentum t ρ θ)) ∈
        complexShellChartDomain t := by
  change 0 < (complexShellRadicand t (complexShellCoordinates _)).re
  rw [complexShellRadicand_coordinates (complexShellBoost_mem_shell t _ _),
    canonicalShellBoost_second_coordinate, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_pos_of_pos (canonicalShellTransverse_pos hρ hθ)

theorem canonicalShellBoost_chart_coordinates {t ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < Real.sin θ) :
    complexShellChart t (complexShellCoordinates
      (complexShellBoost t ((θ : ℂ) * Complex.I) (canonicalShellMomentum t ρ θ))) =
        complexShellBoost t ((θ : ℂ) * Complex.I) (canonicalShellMomentum t ρ θ) := by
  apply complexShellChart_coordinates (complexShellBoost_mem_shell t _ _)
  rw [canonicalShellBoost_second_coordinate, Complex.ofReal_re]
  exact canonicalShellTransverse_pos hρ hθ

/-- Normalized target chart point. -/
noncomputable def normalizedTargetChartPoint (t : ℝ) (z : ComplexSpacetime) (θ : ℝ) :
    ShellEuclideanDomain :=
  shellEuclideanCoordinates.symm (complexShellCoordinates
    (complexShellBoost t ((θ : ℂ) * Complex.I) (normalizedTargetMomentum t z θ)))

theorem normalizedTargetChartPoint_mem_domain {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    normalizedTargetChartPoint t z θ ∈ euclideanShellChartDomain t := by
  change shellEuclideanCoordinates (shellEuclideanCoordinates.symm _) ∈ complexShellChartDomain t
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact canonicalShellBoost_coordinates_mem_domain
    (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)) hθ

theorem normalizedTargetChartPoint_image {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    euclideanLorentzShellChart t (normalizedTargetPreimageMap hz hθ)
      (normalizedTargetChartPoint t z θ) = complexSpacetimeEuclideanEquiv z := by
  simp only [euclideanLorentzShellChart, normalizedTargetChartPoint,
    ContinuousLinearEquiv.apply_symm_apply, lorentzComplexShellChart]
  have hc := canonicalShellBoost_chart_coordinates
    (t := t) (negativeMinkowskiLength_pos (normalizedTarget_real_negative hz)) hθ
  change complexShellChart t (complexShellCoordinates
    (complexShellBoost t ((θ : ℂ) * Complex.I) (normalizedTargetMomentum t z θ))) = _ at hc
  rw [hc]
  exact congrArg complexSpacetimeEuclideanEquiv (normalizedTargetPreimageMap_boost hz hθ)

/-- Actual chart coverage of every point used by the normalized shell
evaluation argument, together with the strict inverse norm margin. -/
theorem normalizedTarget_volume_chart_coverage {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ (Λ : Spacetime ≃L[ℝ] Spacetime) (w : ShellEuclideanDomain),
      IsProperLorentzMap Λ ∧ IsOrthochronousMap Λ ∧
      w ∈ euclideanShellChartDomain t ∧
      euclideanLorentzShellChart t Λ w = complexSpacetimeEuclideanEquiv z ∧
      0 < inducedShellChartDensity t Λ w ∧
      spacetimeEuclideanOperatorNorm Λ.symm < 32 / Real.sin θ := by
  exact ⟨normalizedTargetPreimageMap hz hθ, normalizedTargetChartPoint t z θ,
    normalizedTargetPreimageMap_isProper hz hθ,
    normalizedTargetPreimageMap_isOrthochronous hz hθ,
    normalizedTargetChartPoint_mem_domain hz hθ, normalizedTargetChartPoint_image hz hθ,
    inducedShellChartDensity_pos _ (normalizedTargetChartPoint_mem_domain hz hθ),
    (normalizedTargetPreimageMap_norm_lt hz hθ).2⟩

end VacuumBellSeparation
