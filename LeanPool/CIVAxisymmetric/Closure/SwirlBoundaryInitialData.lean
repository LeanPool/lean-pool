/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.SwirlBoundaryFromAnnulusBound
public import LeanPool.CIVAxisymmetric.Closure.SwirlBoundCutoffDecay
public import LeanPool.CIVAxisymmetric.Reduction.AnalyticInductionBaseCase

/-!
# Initial-time ball bound for the swirl coefficient from smoothness alone

The three theorems below supply the initial-time ball bound `Mi` required by
`CIV.swirl_bound_of_annulus_bound` / `CIV.swirl_bound_ball_of_annulus_bound`
(`eq:aniso:closure:w`) from smoothness of the classical solution alone.  The key
observation is that `u(·, t₀) 1` is continuous on the closed ball
`closure (vec3Ball 0 Rstar) ⊆ vec3Ball 0 1` (`Rstar < 1`), hence bounded there
by the extreme value theorem — exactly the template
`CIV.Reduction.AnalyticInductionBaseCase.exists_bound_of_contDiffOn_zero` already
uses for a scalar field.

This completes the reduction of `CIV.swirl_bound_ball` to a decay bound
`|u_θ| ≤ C_η (−t)^{−η}` from nothing but a classical solution and a plain
order-0 annulus bound.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem exists_abs_apply_one_le_of_contDiffOn_ball {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {Rstar tη : ℝ} (hRpos : 0 < Rstar) (hR1 : Rstar < 1) (htη : tη ∈ Ioo (-1 : ℝ) 0) :
    ∃ Mi : ℝ, 0 ≤ Mi ∧ ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, tη) 1| ≤ Mi := by
  obtain ⟨M', hM'⟩ := exists_bound_of_contDiffOn_zero hRpos hR1
    (contDiffOn_spatialSlice (contDiffOn_component hu 1) htη)
  refine ⟨max M' 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hM' x hx).trans (le_max_left _ _)

theorem swirl_bound_ball_of_annulus_bound_and_contDiffOn
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    {Rlo Rhi t₀ M Rstar : ℝ}
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ M)
    (hR : 0 < Rstar ∧ Rstar < 1) (hRlo : Rlo < Rstar) (hRhi : Rstar < Rhi)
    (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {η : ℝ} (hη : 0 < η)
    (hG : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t)) :
    ∃ Mi : ℝ, 0 ≤ Mi ∧ ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      (x 0 ≠ 0 ∨ x 1 ≠ 0) → (-t) ^ η * |swirlCoeffAt u (x, t)|
        ≤ (-t₀) ^ η * max M Mi + (-t₀) ^ η * Mf * (t - t₀) := by
  obtain ⟨Mi, hMi0, hMi⟩ := exists_abs_apply_one_le_of_contDiffOn_ball
    hsol.1 hR.1 hR.2 ht₀
  refine ⟨Mi, hMi0, swirl_bound_ball_of_annulus_bound u pr f hsol haxi hfaxi Mf hMf
    hbound hR hRlo hRhi ht₀ hη hG hMi⟩

theorem exists_swirlCoeffAt_le_of_annulus_bound
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    {Rlo Rhi t₀ M Rstar : ℝ}
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ M)
    (hR : 0 < Rstar ∧ Rstar < 1) (hRlo : Rlo < Rstar) (hRhi : Rstar < Rhi)
    (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {η : ℝ} (hη : 0 < η)
    (hG : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t)) :
    ∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      (x 0 ≠ 0 ∨ x 1 ≠ 0) → |swirlCoeffAt u (x, t)| ≤ Cη * (-t) ^ (-η) := by
  obtain ⟨Mi, hMi0, hMi_init⟩ := exists_abs_apply_one_le_of_contDiffOn_ball
    hsol.1 hR.1 hR.2 ht₀
  have hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ), |u (x, t) 1| ≤ M :=
    hbdry_of_annulus_bound hbound hRlo hRhi
  exact swirlCoeffAt_le_of_swirl_bound_ball u pr f hsol haxi hfaxi Mf hMf Rstar hR t₀ η ht₀
    hη hG M hbdry Mi hMi_init

end CIV
