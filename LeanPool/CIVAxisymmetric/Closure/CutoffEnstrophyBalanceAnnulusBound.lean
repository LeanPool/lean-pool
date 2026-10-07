/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnstrophyBalance
public import LeanPool.CIVAxisymmetric.Closure.AnnulusBoundsEnstrophy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Cutoff Enstrophy Balance Annulus Bound

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The closed annulus `{x | Rm' ≤ ‖x‖ ∧ ‖x‖ ≤ Rp'}` is closed in the Euclidean topology
on `Vec3`. -/
theorem isClosed_closedAnnulus (Rm' Rp' : ℝ) :
    IsClosed {x : Vec3 | Rm' ≤ vec3EuclideanNorm x ∧ vec3EuclideanNorm x ≤ Rp'} :=
  (isClosed_le continuous_const continuous_vec3EuclideanNorm).inter
    (isClosed_le continuous_vec3EuclideanNorm continuous_const)

/-- When the velocity `u` and its vorticity satisfy a uniform order-≤2
`multiPartial` bound on the open annulus `Rm < ‖x‖ < Rp`, the tested enstrophy
balance `eq:aniso:closure:tested` holds on any closed subset `A` of that annulus,
with `Mu = M` and `Mω = 2M`. This bridges `lem:aniso:annulus`'s open-annulus
multi-index bound to `cutoff_enstrophy_balance`'s closed-set velocity/vorticity
hypotheses `hubd`/`hωbd`. -/
theorem cutoff_enstrophy_balance_of_multiPartial_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (hMf : ForceC2Bounded f)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp M : ℝ} (hM : 0 ≤ M)
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      HasDerivAt (cutoffEnstrophy χ u) (deriv (cutoffEnstrophy χ u) t) t ∧
        (1 / 2) * deriv (cutoffEnstrophy χ u) t + cutoffEnstrophyDissipation χ u t
          ≤ cutoffStretching χ u t + C * (cutoffEnstrophy χ u t + 1) := by
  refine cutoff_enstrophy_balance (hsol := hsol) (hMf := hMf) (hχ := hχ) (hχs := hχs)
    (hχU := hχU) (ht₀ := ht₀) (hAcl := hAcl) (hχA := hχA) (hMu := hM) (Mu := M) (Mω := 2 * M)
    ?_ ?_
  · intro x hx t ht i
    exact (abs_apply_and_vorticityField_le_of_multiPartial_le hbound hM x (hAsub hx).1
      (hAsub hx).2 t ht i).1
  · intro x hx t ht i
    exact (abs_apply_and_vorticityField_le_of_multiPartial_le hbound hM x (hAsub hx).1
      (hAsub hx).2 t ht i).2

/-- The concrete closed sub-annulus `Rm' ≤ ‖x‖ ≤ Rp'` (with `Rm < Rm' ≤ Rp' < Rp`)
is contained in the open annulus `Rm < ‖x‖ < Rp`, so the hypotheses of
`cutoff_enstrophy_balance_of_multiPartial_le` are satisfied. This is the instance
needed when a cutoff's gradient support occupies a closed annulus. -/
theorem cutoff_enstrophy_balance_of_multiPartial_le_closedAnnulus
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (hMf : ForceC2Bounded f)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {Rm Rm' Rp' Rp M : ℝ} (hM : 0 ≤ M) (hRm : Rm < Rm') (hRp : Rp' < Rp)
    (hχA : ∀ x : Vec3, x ∉ {x : Vec3 | Rm' ≤ vec3EuclideanNorm x ∧ vec3EuclideanNorm x ≤ Rp'} →
      fderiv ℝ χ x = 0)
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      HasDerivAt (cutoffEnstrophy χ u) (deriv (cutoffEnstrophy χ u) t) t ∧
        (1 / 2) * deriv (cutoffEnstrophy χ u) t + cutoffEnstrophyDissipation χ u t
          ≤ cutoffStretching χ u t + C * (cutoffEnstrophy χ u t + 1) := by
  have hAsub : {x : Vec3 | Rm' ≤ vec3EuclideanNorm x ∧ vec3EuclideanNorm x ≤ Rp'} ⊆
      {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp} := by
    intro x ⟨hx1, hx2⟩
    exact ⟨lt_of_lt_of_le hRm hx1, lt_of_le_of_lt hx2 hRp⟩
  exact cutoff_enstrophy_balance_of_multiPartial_le hsol hMf hχ hχs hχU ht₀
    (isClosed_closedAnnulus Rm' Rp') hχA hM hAsub hbound

end CIV
