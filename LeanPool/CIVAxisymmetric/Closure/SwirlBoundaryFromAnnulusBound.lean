/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.SwirlBound
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Boundary data for the swirl bound from an annulus bound

The two theorems below supply the parabolic-boundary hypothesis `hbdry` of
`swirl_bound` / `swirl_bound_ball` (`eq:aniso:closure:w`) from a plain order-0 bound on
a space–time annulus that contains the sphere `|x| = Rstar`. The first lemma deduces the
pointwise estimate `|u (x, t) 1| ≤ M` on the sphere from the annulus bound
`hbound` using `abs_apply_le_vec3EuclideanNorm`. The two main theorems then instantiate
`swirl_bound` / `swirl_bound_ball` with this `hbdry`, taking `Mb := M` and preserving
`Mi` as given by `hinit`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem hbdry_of_annulus_bound {u : ParabolicPoint → Vec3} {Rlo Rhi t₀ M Rstar : ℝ}
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ M)
    (hRlo : Rlo < Rstar) (hRhi : Rstar < Rhi) :
    ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo t₀ (0 : ℝ), |u (x, t) 1| ≤ M := by
  intro x hx t ht
  have h1 : Rlo < vec3EuclideanNorm x := by rwa [hx]
  have h2 : vec3EuclideanNorm x < Rhi := by rwa [hx]
  have hnorm := hbound x h1 h2 t ht
  exact (abs_apply_le_vec3EuclideanNorm (u (x, t)) 1).trans hnorm

theorem swirl_bound_of_annulus_bound
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
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t))
    {Mi : ℝ} (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, t₀) 1| ≤ Mi) :
    ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
      (-t) ^ η * |u (meridional x₁ x₃, t) 1|
        ≤ (-t₀) ^ η * max M Mi + (-t₀) ^ η * Mf * (t - t₀) := by
  exact swirl_bound u pr f hsol haxi hfaxi Mf hMf Rstar hR t₀ η ht₀ hη hG M
    (hbdry_of_annulus_bound hbound hRlo hRhi) Mi hinit

theorem swirl_bound_ball_of_annulus_bound
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
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t))
    {Mi : ℝ} (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, t₀) 1| ≤ Mi) :
    ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar, (x 0 ≠ 0 ∨ x 1 ≠ 0) →
      (-t) ^ η * |swirlCoeffAt u (x, t)|
        ≤ (-t₀) ^ η * max M Mi + (-t₀) ^ η * Mf * (t - t₀) := by
  exact swirl_bound_ball u pr f hsol haxi hfaxi Mf hMf Rstar hR t₀ η ht₀ hη hG M
    (hbdry_of_annulus_bound hbound hRlo hRhi) Mi hinit

end CIV
