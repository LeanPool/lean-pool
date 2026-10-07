/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnergyInequalityGronwallChain
public import LeanPool.CIVAxisymmetric.Closure.EnstrophyRegularityFacts

/-!
`closure_enstrophy_decay_of_exists_energy_inequality` is
`exists_closure_gronwall_bound_of_exists_energy_inequality` for the cutoff enstrophy
`cutoffEnstrophy χ u` and its dissipation `cutoffEnstrophyDissipation χ u`: it composes the
substitution step `deriv_le_of_closure_energy` of `eq:aniso:closure:energy` with the Grönwall step
`closure_gronwall_bound` of `lem:aniso:closure`, so that the energy inequality in the form
`∃ Cstar ≥ 1, …` together with the `G`, `W` decay data gives the enstrophy decay
`Y + 1 ≤ C' (−t)^{−C_*η}`. `closure_enstrophy_decay_sixteenth_eta_of_exists_energy_inequality` is
the specialization to the manuscript's choice `η = 1/(16 C_*)`, for which the decay exponent is
the universal constant `1/16` (`exists_closure_gronwall_bound_sixteenth_eta`), and
`closure_enstrophy_decay_of_mixed_term_bound` obtains the energy inequality from
`CIV.energy_inequality_of_mixed_term_bound`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem closure_enstrophy_decay_of_exists_energy_inequality
    {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1)
    {tη η Cη : ℝ} (htη : tη ∈ Ioo (-1 : ℝ) 0) (hη : 0 < η ∧ 2 * η < 1) (hCη : 0 ≤ Cη)
    {G W : ℝ → ℝ}
    (hG : ∀ t ∈ Ioo tη (0 : ℝ), G t ≤ η / (-t))
    (hW0 : ∀ t ∈ Ioo tη (0 : ℝ), 0 ≤ W t)
    (hW : ∀ t ∈ Ioo tη (0 : ℝ), W t ≤ Cη * (-t) ^ (-η))
    (hex : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ t ∈ Ioo tη (0 : ℝ),
      deriv (cutoffEnstrophy χ u) t + cutoffEnstrophyDissipation χ u t
        ≤ Cstar * (G t + W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ t ∈ Ioo tη (0 : ℝ), cutoffEnstrophy χ u t + 1 ≤ C' * (-t) ^ (-(Cstar * η)) := by
  exact exists_closure_gronwall_bound_of_exists_energy_inequality htη.2 hη hCη
    (fun t ht => cutoffEnstrophyDissipation_nonneg χ u t)
    (fun t ht => cutoffEnstrophy_nonneg χ u t)
    hG hW0 hW
    (fun t ht => continuousOn_cutoffEnstrophy hu hχ hχs hχU htη ht)
    (fun t ht => hasDerivWithinAt_Ici_cutoffEnstrophy hu hχ hχs hχU htη ht)
    (cutoffEnstrophy_nonneg χ u tη)
    hex

theorem closure_enstrophy_decay_sixteenth_eta_of_exists_energy_inequality
    {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1)
    {tη Cη : ℝ} (htη : tη ∈ Ioo (-1 : ℝ) 0) (hCη : 0 ≤ Cη)
    {G W : ℝ → ℝ}
    (hW0 : ∀ t ∈ Ioo tη (0 : ℝ), 0 ≤ W t)
    (hex : ∃ Cstar : ℝ, 1 ≤ Cstar ∧
      (∀ t ∈ Ioo tη (0 : ℝ), deriv (cutoffEnstrophy χ u) t + cutoffEnstrophyDissipation χ u t
        ≤ Cstar * (G t + W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1)) ∧
      (∀ t ∈ Ioo tη (0 : ℝ), G t ≤ (1 / (16 * Cstar)) / (-t)) ∧
      (∀ t ∈ Ioo tη (0 : ℝ), W t ≤ Cη * (-t) ^ (-(1 / (16 * Cstar))))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Ioo tη (0 : ℝ),
      cutoffEnstrophy χ u t + 1 ≤ C' * (-t) ^ (-(1 / 16 : ℝ)) := by
  exact exists_closure_gronwall_bound_sixteenth_eta htη.2 hCη
    (fun t ht => cutoffEnstrophyDissipation_nonneg χ u t)
    (fun t ht => cutoffEnstrophy_nonneg χ u t)
    hW0
    (fun t ht => continuousOn_cutoffEnstrophy hu hχ hχs hχU htη ht)
    (fun t ht => hasDerivWithinAt_Ici_cutoffEnstrophy hu hχ hχs hχU htη ht)
    (cutoffEnstrophy_nonneg χ u tη)
    hex

theorem closure_enstrophy_decay_of_mixed_term_bound
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (hMf : ForceC2Bounded f)
    (haxi : IsAxisymmetricOn u unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {tη : ℝ} (htη : tη ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Mu Mω : ℝ} (hMu : 0 ≤ Mu)
    (hubd : ∀ x ∈ A, ∀ t ∈ Ioo tη (0 : ℝ), ∀ i : Fin 3, |u (x, t) i| ≤ Mu)
    (hωbd : ∀ x ∈ A, ∀ t ∈ Ioo tη (0 : ℝ), ∀ i : Fin 3, |vorticityField u (x, t) i| ≤ Mω)
    {Mix : ℝ → ℝ} {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hsplit : ∀ t ∈ Ioo tη (0 : ℝ), cutoffStretching χ u t
      = (∫ x : Vec3, χ x ^ 2 * stretchGTerm u x t) + Mix t
        - ∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
            * curlComp u 1 (meridional (polarR x) (x 2), t)))
    {G W : ℝ → ℝ} (hGnn : ∀ t, 0 ≤ G t)
    (hG : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        meridionalQuantity u (meridional x₁ x₃, t) ≤ G t)
    (hW : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W t)
    (hmix : ∀ t ∈ Ioo tη (0 : ℝ), Mix t ≤ (1 / 4) * cutoffEnstrophyDissipation χ u t
      + Cm * (W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1))
    {η Cη : ℝ} (hη : 0 < η ∧ 2 * η < 1) (hCη : 0 ≤ Cη)
    (hGη : ∀ t ∈ Ioo tη (0 : ℝ), G t ≤ η / (-t))
    (hW0 : ∀ t ∈ Ioo tη (0 : ℝ), 0 ≤ W t)
    (hWη : ∀ t ∈ Ioo tη (0 : ℝ), W t ≤ Cη * (-t) ^ (-η)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ t ∈ Ioo tη (0 : ℝ), cutoffEnstrophy χ u t + 1 ≤ C' * (-t) ^ (-(Cstar * η)) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1 := hρU.trans hρ1
  have hex := energy_inequality_of_mixed_term_bound hsol hMf haxi hχ hχs hρU hρ1 htη hAcl hχA hMu
    hubd hωbd hCm hsplit hGnn hG hW hmix
  exact closure_enstrophy_decay_of_exists_energy_inequality hu hχ hχs hχU htη hη hCη hGη hW0 hWη hex

end CIV
