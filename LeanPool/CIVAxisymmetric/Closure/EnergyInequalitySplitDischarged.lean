/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnergyInequalityOfMixedTerm
public import LeanPool.CIVAxisymmetric.Closure.StretchingSplitIntegrated

/-!
# The tested energy inequality with the stretching splitting supplied

`energy_inequality_of_mixed_term_bound` assembles `eq:aniso:closure:energy` from the
enstrophy balance and the two stretching estimates, carrying the splitting of the tested
stretching term as a hypothesis.  That splitting is now proved
(`cutoffStretching_eq_stretchGTerm_add_mixed_sub_angular`), so it is supplied here and the
mixed term is the concrete integral `I(t) = ∫ χ² (∂_r u_z) ω_r ω_z` of
`eq:aniso:closure:mixed`.  What remains carried is the bound on that integral,
`eq:aniso:closure:mixed:bound`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- **`eq:aniso:closure:energy`** with the stretching splitting discharged: the only
remaining hypothesis of the assembly is the bound on the mixed term
`I(t) = ∫ χ² (∂_r u_z) ω_r ω_z` of `eq:aniso:closure:mixed`. -/
theorem energy_inequality_of_mixed_term_bound_of_split
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (hMf : ForceC2Bounded f)
    (haxi : IsAxisymmetricOn u unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Mu Mω : ℝ} (hMu : 0 ≤ Mu)
    (hubd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ 0, ∀ i : Fin 3, |u (x, t) i| ≤ Mu)
    (hωbd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ 0, ∀ i : Fin 3, |vorticityField u (x, t) i| ≤ Mω)
    {Cm : ℝ} (hCm : 0 ≤ Cm)
    {G W : ℝ → ℝ} (hGnn : ∀ t, 0 ≤ G t)
    (hG : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        meridionalQuantity u (meridional x₁ x₃, t) ≤ G t)
    (hW : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W t)
    (hmix : ∀ t ∈ Ioo t₀ (0 : ℝ), (∫ x : Vec3, χ x ^ 2 * stretchMixedTerm u x t)
      ≤ (1 / 4) * cutoffEnstrophyDissipation χ u t
        + Cm * (W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      deriv (cutoffEnstrophy χ u) t + cutoffEnstrophyDissipation χ u t
        ≤ Cstar * (G t + W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hsplit : ∀ t ∈ Ioo t₀ (0 : ℝ), cutoffStretching χ u t
      = (∫ x : Vec3, χ x ^ 2 * stretchGTerm u x t)
        + (∫ x : Vec3, χ x ^ 2 * stretchMixedTerm u x t)
        - ∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
            * curlComp u 1 (meridional (polarR x) (x 2), t)) := by
    intro t ht
    exact cutoffStretching_eq_stretchGTerm_add_mixed_sub_angular haxi hu hχ hχs
      (hρU.trans hρ1) ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  exact energy_inequality_of_mixed_term_bound hsol hMf haxi hχ hχs hρU hρ1 ht₀ hAcl hχA
    hMu hubd hωbd hCm hsplit hGnn hG hW hmix

end CIV
