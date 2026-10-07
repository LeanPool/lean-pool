/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.AnnulusBoundsEnstrophy
public import LeanPool.CIVAxisymmetric.Closure.SwirlBoundaryFromAnnulusBound

/-!
# Euclidean-norm annulus bound from per-component `multiPartial` bounds

`lem:aniso:annulus` supplies order-`≤2` per-component `multiPartial` bounds on the regular
annulus. The two theorems below bridge that per-component form to the Euclidean-norm form
that `swirl_bound_of_annulus_bound` (`eq:aniso:closure:w`) requires: the first supplies the
direct conversion, the second applies it to obtain the swirl bound `eq:aniso:closure:w`
without a separate norm-form hypothesis on the annulus.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem exists_vec3EuclideanNorm_bound_of_multiPartial_le
    {u : ParabolicPoint → Vec3} {Rm Rp t₀ M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ M) :
    ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ 3 * M := by
  intro x hxRm hxRp t ht
  refine le_trans (vec3EuclideanNorm_le_sum_abs (u (x, t))) ?_
  have hi : ∀ i : Fin 3, |u (x, t) i| ≤ M := by
    intro i
    have h := hbound x hxRm hxRp t ht i (fun _ => 0) (by norm_num)
    have hM_abs : |M| = M := abs_of_nonneg hM
    simpa [multiPartial, hM_abs] using h
  calc
    ∑ i : Fin 3, |u (x, t) i| ≤ ∑ i : Fin 3, M :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = (Finset.card (Finset.univ : Finset (Fin 3)) : ℝ) * M := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = 3 * M := by simp

/-!
The Euclidean-norm swirl bound `eq:aniso:closure:w` derived directly from
`lem:aniso:annulus`'s own order-`≤2` per-component conclusion, without a separate
norm-form hypothesis on the annulus.
-/
theorem swirl_bound_of_annulus_bound_of_multiPartial_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (Mf : ℝ) (hMf : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf)
    {Rlo Rhi t₀ M Rstar : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ M)
    (hR : 0 < Rstar ∧ Rstar < 1) (hRlo : Rlo < Rstar) (hRhi : Rstar < Rhi)
    (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {η : ℝ} (hη : 0 < η)
    (hG : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t))
    {Mi : ℝ} (hinit : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, |u (x, t₀) 1| ≤ Mi) :
    ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
      (-t) ^ η * |u (meridional x₁ x₃, t) 1|
        ≤ (-t₀) ^ η * max (3 * M) Mi + (-t₀) ^ η * Mf * (t - t₀) := by
  exact swirl_bound_of_annulus_bound u p f hsol haxi hfaxi Mf hMf
    (fun x hx1 hx2 t ht =>
      exists_vec3EuclideanNorm_bound_of_multiPartial_le hM hbound x hx1 hx2 t ht)
    hR hRlo hRhi ht₀ hη hG (Mi := Mi) hinit

end CIV
