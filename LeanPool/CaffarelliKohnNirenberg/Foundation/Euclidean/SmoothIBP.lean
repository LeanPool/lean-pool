/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts for spatial derivatives

The weak-form integration by parts identity
`∫ u ∂_i φ = -∫ ∂_i u φ` for smooth compactly supported functions on `Vec3`.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN



/-- Integration by parts for a single spatial derivative:
`∫ u (∂_i φ) = -∫ (∂_i u) φ` for smooth `u`, `φ` with compactly supported `φ`. -/
theorem integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
    {u φ : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin 3) :
    ∫ x, u x * spatialDeriv φ i x = -∫ x, spatialDeriv u i x * φ x := by
  have hφd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv φ i) :=
    contDiff_spatialDeriv_smooth hφ i
  have hud : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv u i) :=
    contDiff_spatialDeriv_smooth hu i
  have hφdc : HasCompactSupport (spatialDeriv φ i) := by
    change HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i))
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hleft : Integrable (fun x => u x * spatialDeriv φ i x) volume :=
    (hu.continuous.mul hφd.continuous).integrable_of_hasCompactSupport
      (hφdc.mul_left (f := u))
  have hright : Integrable (fun x => spatialDeriv u i x * φ x) volume :=
    (hud.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (hφc.mul_left (f := spatialDeriv u i))
  have hprod : Integrable (fun x => u x * φ x) volume :=
    (hu.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (hφc.mul_left (f := u))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (v := basisVec i) hright hleft hprod
    (fun x _ => hu.differentiable (by norm_num) x)
    (fun x _ => hφ.differentiable (by norm_num) x)
  simpa only [spatialDeriv] using h

end CKN
