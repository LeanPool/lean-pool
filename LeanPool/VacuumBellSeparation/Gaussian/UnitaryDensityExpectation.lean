/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryTrace
public import LeanPool.VacuumBellSeparation.Gaussian.DensityExpectationIndependence

/-!
# Unitary covariance of the actual complex density functional

The square-root basis series transforms term by term in the transported
Hilbert basis. The already proved basis independence extends the result
to any target basis. These identities concern the genuine complex
expectation on all bounded operators, not a positive trace evaluated at
a potentially nonpositive product.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

variable {E F ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem conjStarAlgEquiv_sqrt (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    e.conjStarAlgEquiv (CFC.sqrt A) = CFC.sqrt (e.conjStarAlgEquiv A) := by
  simpa only [CFC.sqrt_eq_rpow] using
    conjStarAlgEquiv_rpow e hA (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem densityExpectation_transported_basis (e : E ≃ₗᵢ[ℂ] F) (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) (B : E →L[ℂ] E) :
    densityExpectation (transportedHilbertBasis b e) (e.conjStarAlgEquiv A) (e.conjStarAlgEquiv B) =
      densityExpectation b A B := by
  simp only [densityExpectation, familyExpectation, ← conjStarAlgEquiv_sqrt e hA,
    transportedHilbertBasis_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    e.symm_apply_apply, e.inner_map_map]

theorem densityExpectation_conjStarAlgEquiv (e : E ≃ₗᵢ[ℂ] F)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) (B : E →L[ℂ] E) :
    densityExpectation c (e.conjStarAlgEquiv A) (e.conjStarAlgEquiv B) =
      densityExpectation b A B := by
  rw [densityExpectation_eq c (transportedHilbertBasis b e)
    (IsPositiveTraceClass.conjStarAlgEquiv e hA)]
  exact densityExpectation_transported_basis e b hA.1 B

theorem densityExpectation_conjStarAlgEquiv_left (e : E ≃ₗᵢ[ℂ] F)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) (B : F →L[ℂ] F) :
    densityExpectation c (e.conjStarAlgEquiv A) B =
      densityExpectation b A (e.conjStarAlgEquiv.symm B) := by
  have h := densityExpectation_conjStarAlgEquiv e b c hA (e.conjStarAlgEquiv.symm B)
  simpa only [StarAlgEquiv.apply_symm_apply] using h

theorem densityExpectation_symm_conjStarAlgEquiv_left (e : E ≃ₗᵢ[ℂ] F)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    {A : F →L[ℂ] F} (hA : IsPositiveTraceClass A) (B : E →L[ℂ] E) :
    densityExpectation b (e.symm.conjStarAlgEquiv A) B =
      densityExpectation c A (e.conjStarAlgEquiv B) := by
  have h := densityExpectation_conjStarAlgEquiv_left e.symm c b hA B
  simpa only [LinearIsometryEquiv.symm_conjStarAlgEquiv, LinearIsometryEquiv.symm_symm] using h

end VacuumBellSeparation.Gaussian
