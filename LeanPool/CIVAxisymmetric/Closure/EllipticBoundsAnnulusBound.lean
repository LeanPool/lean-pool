/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EllipticBoundsApply
public import LeanPool.CIVAxisymmetric.Closure.EllipticBoundsSecond

/-!
# `eq:aniso:closure:elliptic` with velocity-bound hypotheses discharged from an annulus bound

This file specialises the two elliptic bounds of `eq:aniso:closure:elliptic` (the gradient
and Hessian estimates of `lem:aniso:closure`) to the situation where the velocity bounds on the
closed set `A` come directly from an order‑≤2 `multiPartial` annulus bound of
`lem:aniso:annulus`, bypassing the need to supply separate `hubd`/`hubd2` hypotheses.

The three commutator witnesses (`integral_cutoff_sq_fderiv_le`,
`integral_cutoff_sq_fderiv_fderiv_le`, `integral_sq_fderiv_fderiv_smul_le`) are already stated
in their respective source modules and are applied here without redefinition. Only the annulus
subset `A` and the cutoff data remain abstract, following the same pattern as
`CIV.cutoff_enstrophy_balance_of_multiPartial_le` in `CutoffEnstrophyBalanceAnnulusBound.lean`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem integral_cutoff_sq_spatialPartial_le_of_multiPartial_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ}
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => u w i) j (x, t)) ^ 2)
        ≤ C * (cutoffEnstrophy χ u t + 1) := by
  have hubd' : ∀ x ∈ A, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, |u (x, t) i| ≤ Mu := by
    intro x hx t ht i
    have hα0 : ((fun _ : Fin 3 => (0 : ℕ)) 0 + (fun _ : Fin 3 => (0 : ℕ)) 1
        + (fun _ : Fin 3 => (0 : ℕ)) 2 ≤ 2) := by norm_num
    simpa [multiPartial] using hbound x (hAsub hx).1 (hAsub hx).2 t ht i (fun _ => 0) hα0
  exact integral_cutoff_sq_spatialPartial_le hsol hχ hχs hρU hρ1 ht₀ hAcl hχA hubd'
    integral_cutoff_sq_fderiv_le

theorem integral_cutoff_sq_spatialSecondPartial_le_of_multiPartial_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ}
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2)
        ≤ C * (cutoffEnstrophyDissipation χ u t + 1) := by
  have hubd' : ∀ x ∈ A, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, |u (x, t) i| ≤ Mu := by
    intro x hx t ht i
    have hα0 : ((fun _ : Fin 3 => (0 : ℕ)) 0 + (fun _ : Fin 3 => (0 : ℕ)) 1
        + (fun _ : Fin 3 => (0 : ℕ)) 2 ≤ 2) := by norm_num
    simpa [multiPartial] using hbound x (hAsub hx).1 (hAsub hx).2 t ht i (fun _ => 0) hα0
  have hubd2' : ∀ x ∈ A, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ,
      α 0 + α 1 + α 2 ≤ 2 → |multiPartial (fun w => u w i) α (x, t)| ≤ Mu := by
    intro x hx t ht i α hα
    exact hbound x (hAsub hx).1 (hAsub hx).2 t ht i α hα
  exact integral_cutoff_sq_spatialSecondPartial_le hsol hχ hχs hρU hρ1 ht₀ hAcl hχA hubd'
    hubd2' integral_cutoff_sq_fderiv_fderiv_le integral_sq_fderiv_fderiv_smul_le

theorem exists_C_cutoff_sq_spatialPartial_and_spatialSecondPartial_le_of_multiPartial_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ}
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      ((∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => u w i) j (x, t)) ^ 2)
        ≤ C * (cutoffEnstrophy χ u t + 1)) ∧
      ((∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2)
        ≤ C * (cutoffEnstrophyDissipation χ u t + 1)) := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ :=
    integral_cutoff_sq_spatialPartial_le_of_multiPartial_le
      hsol hχ hχs hρU hρ1 ht₀ hAcl hχA hAsub hbound
  obtain ⟨C₂, hC₂nn, hC₂⟩ :=
    integral_cutoff_sq_spatialSecondPartial_le_of_multiPartial_le
      hsol hχ hχs hρU hρ1 ht₀ hAcl hχA hAsub hbound
  have hYpos : ∀ t : ℝ, 0 ≤ cutoffEnstrophy χ u t + 1 := by
    intro t
    have hnn : 0 ≤ cutoffEnstrophy χ u t := by
      rw [cutoffEnstrophy_eq_integral_sq_curlVec]
      exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
        sq_nonneg _)
    linarith only [hnn]
  have hMpos : ∀ t : ℝ, 0 ≤ cutoffEnstrophyDissipation χ u t + 1 := by
    intro t
    have hnn : 0 ≤ cutoffEnstrophyDissipation χ u t := by
      rw [cutoffEnstrophyDissipation_eq_integral_sq_fderiv_curlVec]
      exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)
    linarith only [hnn]
  have hCmax : 0 ≤ max C₁ C₂ := hC₁nn.trans (le_max_left _ _)
  refine ⟨max C₁ C₂, hCmax, fun t ht => ?_⟩
  have h₁ : (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialPartial (fun w => u w i) j (x, t)) ^ 2)
      ≤ C₁ * (cutoffEnstrophy χ u t + 1) := hC₁ t ht
  have h₂ : (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2)
      ≤ C₂ * (cutoffEnstrophyDissipation χ u t + 1) := hC₂ t ht
  have h₁' : C₁ * (cutoffEnstrophy χ u t + 1) ≤ max C₁ C₂ * (cutoffEnstrophy χ u t + 1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (hYpos t)
  have h₂' : C₂ * (cutoffEnstrophyDissipation χ u t + 1) ≤ max C₁ C₂ *
    (cutoffEnstrophyDissipation χ u t + 1) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (hMpos t)
  exact ⟨le_trans h₁ h₁', le_trans h₂ h₂'⟩

end CIV
