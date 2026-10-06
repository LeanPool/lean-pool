/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.MixedTermClosure
public import LeanPool.CIVAxisymmetric.Closure.EnergyInequalitySplitDischarged
public import LeanPool.CIVAxisymmetric.Closure.AnnulusBoundsEnstrophy

/-!
# The tested enstrophy inequality `eq:aniso:closure:energy` of `lem:aniso:closure`

This closes by one application of `energy_inequality_of_mixed_term_bound_of_split`, whose
`hsplit` hypothesis is already discharged there
(`cutoffStretching_eq_stretchGTerm_add_mixed_sub_angular`)
and whose only remaining hypothesis, the mixed-term bound `hmix`, is exactly
`step_closure_mixed_term`'s conclusion. Both draw their velocity/vorticity bounds from the same
order-`≤ 2` annulus data of `lem:aniso:annulus`: the order-`0` bounds `hubd`, `hωbd` that
`energy_inequality_of_mixed_term_bound_of_split` needs are one clause of
`abs_apply_and_vorticityField_le_of_multiPartial_le` applied to that same data, so nothing new
is carried.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- **`eq:aniso:closure:energy`.** For a classical solution with a `C²`-bounded force, a cutoff
`χ` supported in `B(ρ)`, `0 < ρ`, order-`≤ 2` derivative bounds for `u` on the closed annulus
`A` carrying `∇χ`, a meridional bound `G` and a swirl bound `W` on `B(ρ)`, there is `C_* ≥ 1`
with `dY/dt + M ≤ C_* (G + W² + 1) (Y + 1)` on `(t₀, 0)`. -/
theorem step_closure_energy_inequality
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (hMf : ForceC2Bounded f)
    (haxi : IsAxisymmetricOn u unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1) (hρpos : 0 < ρ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ} (hMu : 0 ≤ Mu)
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu)
    {G W : ℝ → ℝ} (hGnn : ∀ t, 0 ≤ G t)
    (hG : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        meridionalQuantity u (meridional x₁ x₃, t) ≤ G t)
    (hW : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W t) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      deriv (cutoffEnstrophy χ u) t + cutoffEnstrophyDissipation χ u t
        ≤ Cstar * (G t + W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1) := by
  have hubd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, |u (x, t) i| ≤ Mu := by
    intro x hx t ht i
    exact (abs_apply_and_vorticityField_le_of_multiPartial_le hbound hMu x
      (hAsub hx).1 (hAsub hx).2 t ht i).1
  have hωbd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3,
      |vorticityField u (x, t) i| ≤ 2 * Mu := by
    intro x hx t ht i
    exact (abs_apply_and_vorticityField_le_of_multiPartial_le hbound hMu x
      (hAsub hx).1 (hAsub hx).2 t ht i).2
  obtain ⟨Cm, hCmnn, hmix⟩ := step_closure_mixed_term hsol haxi hχ hχs hρU hρ1 hρpos ht₀ hAcl
    hχA hMu hAsub hbound hW
  exact energy_inequality_of_mixed_term_bound_of_split hsol hMf haxi hχ hχs hρU hρ1 ht₀ hAcl
    hχA hMu hubd hωbd hCmnn hGnn hG hW (fun t ht => le_trans (le_abs_self _) (hmix t ht))

end CIV
