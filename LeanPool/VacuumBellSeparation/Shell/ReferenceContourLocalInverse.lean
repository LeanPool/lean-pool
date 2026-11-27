/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ReferenceContourDerivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Actual local inverse for the six selected contour parameters

The inverse-function theorem is applied to the real six-dimensional
map already differentiated. This is a local section in free shell
coordinates, with no coarea or measure conclusion included.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Reference contour derivative equivalence of type `(Fin 6 → ℝ) ≃L[ℝ] (Fin 3 → ℂ)`. -/
noncomputable def referenceContourDerivativeEquiv (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) : (Fin 6 → ℝ) ≃L[ℝ] (Fin 3 → ℂ) :=
  referenceContourTangentEquiv
    (radialShellEnergy m B 0 * Real.cos θ) B (radialShellEnergy m B 0 * Real.sin θ)
    (B / radialShellEnergy m B 0 * Real.cos θ)
    (B / radialShellEnergy m B 0 * Real.sin θ)
    hB.ne' (mul_pos (radialShellEnergy_pos hB m) hθ).ne'
    (mul_pos (div_pos hB (radialShellEnergy_pos hB m)) hθ).ne'

theorem referenceContourDerivativeEquiv_coe (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    (referenceContourDerivativeEquiv m hB hθ : (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℂ)) =
      referenceContourDerivative m B θ := by
  ext a i
  rfl

theorem hasStrictFDerivAt_referenceContourMap (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    HasStrictFDerivAt (referenceContourMap m B θ)
      (referenceContourDerivativeEquiv m hB hθ : (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℂ)) 0 := by
  rw [referenceContourDerivativeEquiv_coe]
  exact (contDiffAt_referenceContourMap hB m θ).hasStrictFDerivAt
    (hasFDerivAt_referenceContourMap hB m θ) (by simp)

/-- Reference contour local chart. -/
noncomputable def referenceContourLocalChart (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    OpenPartialHomeomorph (Fin 6 → ℝ) (Fin 3 → ℂ) :=
  (hasStrictFDerivAt_referenceContourMap m hB hθ).toOpenPartialHomeomorph
    (referenceContourMap m B θ)

@[simp] theorem referenceContourLocalChart_apply (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (a : Fin 6 → ℝ) :
    referenceContourLocalChart m hB hθ a = referenceContourMap m B θ a := rfl

theorem zero_mem_referenceContourLocalChart (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    0 ∈ (referenceContourLocalChart m hB hθ).source :=
  (hasStrictFDerivAt_referenceContourMap m hB hθ).mem_toOpenPartialHomeomorph_source

theorem referenceContourLocalChart_center_mem_target (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    complexShellCoordinates (radialShellContour m B θ 0) ∈
      (referenceContourLocalChart m hB hθ).target := by
  have h := (hasStrictFDerivAt_referenceContourMap m hB hθ).image_mem_toOpenPartialHomeomorph_target
  have ha : activeLorentzParameters 0 = 0 := by ext i; fin_cases i <;> rfl
  simpa only [referenceContourLocalChart, referenceContourMap, ha,
    Pi.zero_apply, complexLorentzFamilyAction_zero] using h

theorem referenceContourLocalChart_inverse_derivative (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    HasStrictFDerivAt (referenceContourLocalChart m hB hθ).symm
      ((referenceContourDerivativeEquiv m hB hθ).symm :
        (Fin 3 → ℂ) →L[ℝ] (Fin 6 → ℝ)) (referenceContourMap m B θ 0) :=
  (hasStrictFDerivAt_referenceContourMap m hB hθ).to_localInverse

end VacuumBellSeparation
