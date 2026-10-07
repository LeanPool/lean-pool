/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnstrophyBalance
public import LeanPool.CIVAxisymmetric.Closure.StretchingBounds

/-!
# Energy Inequality Of Mixed Term

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

private lemma closure_energy_arith (C Cm g w y m d s gt mx an : ℝ)
    (hC : 0 ≤ C) (hCm : 0 ≤ Cm) (hg : 0 ≤ g) (hw : 0 ≤ w) (hy : 0 ≤ y)
    (h1 : (1 / 2) * d + m ≤ s + C * (y + 1)) (h2 : s = gt + mx - an)
    (h3 : gt ≤ 2 * g * y) (h4 : -an ≤ (1 / 4) * m + 4 * w * y)
    (h5 : mx ≤ (1 / 4) * m + Cm * (w + 1) * (y + 1)) :
    d + m ≤ (12 + 2 * Cm + 2 * C) * (g + w + 1) * (y + 1) := by
  have hstep : d + m ≤ 4 * (g * y) + 2 * (Cm * ((w + 1) * (y + 1))) + 8 * (w * y)
      + 2 * (C * (y + 1)) := by nlinarith only [h1, h2, h3, h4, h5]
  have b1 : g * y ≤ (g + w + 1) * (y + 1) := by nlinarith only [hg, hw, hy]
  have b2 : w * y ≤ (g + w + 1) * (y + 1) := by nlinarith only [hg, hw, hy]
  have b3 : (w + 1) * (y + 1) ≤ (g + w + 1) * (y + 1) := by nlinarith only [hg, hy]
  have b4 : y + 1 ≤ (g + w + 1) * (y + 1) := by nlinarith only [hg, hw, hy]
  have c3 : Cm * ((w + 1) * (y + 1)) ≤ Cm * ((g + w + 1) * (y + 1)) :=
    mul_le_mul_of_nonneg_left b3 hCm
  have c4 : C * (y + 1) ≤ C * ((g + w + 1) * (y + 1)) :=
    mul_le_mul_of_nonneg_left b4 hC
  nlinarith only [hstep, b1, b2, c3, c4]

/-- **`eq:aniso:closure:energy`, the tested enstrophy inequality of `lem:aniso:closure`,
conditioned on the mixed-term bound of `eq:aniso:closure:mixed:bound` and on the splitting of the
tested stretching term, both taken as explicit hypotheses.** Both are proved separately: the
splitting is supplied in `energy_inequality_of_mixed_term_bound_of_split`, and the mixed-term
bound is `step_closure_mixed_term`.

The three pieces — `cutoff_enstrophy_balance`, `stretchGTerm_integral_le`,
`stretchAngularTerm_integral_abs_le` — are assembled into the exact shape
`deriv Y + M ≤ C_*(G + W² + 1)(Y + 1)`. -/
theorem energy_inequality_of_mixed_term_bound
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
    {Mix : ℝ → ℝ} {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hsplit : ∀ t ∈ Ioo t₀ (0 : ℝ), cutoffStretching χ u t
      = (∫ x : Vec3, χ x ^ 2 * stretchGTerm u x t) + Mix t
        - ∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
            * curlComp u 1 (meridional (polarR x) (x 2), t)))
    {G W : ℝ → ℝ} (hGnn : ∀ t, 0 ≤ G t)
    (hG : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        meridionalQuantity u (meridional x₁ x₃, t) ≤ G t)
    (hW : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W t)
    (hmix : ∀ t ∈ Ioo t₀ (0 : ℝ), Mix t ≤ (1 / 4) * cutoffEnstrophyDissipation χ u t
      + Cm * (W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      deriv (cutoffEnstrophy χ u) t + cutoffEnstrophyDissipation χ u t
        ≤ Cstar * (G t + W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  obtain ⟨C, hC0, hbal⟩ := cutoff_enstrophy_balance hsol hMf hχ hχs (hρU.trans hρ1) ht₀ hAcl
    hχA hMu hubd hωbd
  refine ⟨12 + 2 * Cm + 2 * C, by linarith only [hC0, hCm], fun t ht => ?_⟩
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hYnn : (0 : ℝ) ≤ cutoffEnstrophy χ u t :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg (χ x))
      (Finset.sum_nonneg (fun i _ => sq_nonneg (vorticityField u (x, t) i))))
  have hstretch := stretchGTerm_integral_le haxi hu hχ hχs hρU hρ1 htmem (hG t ht) (hGnn t)
  have hang := stretchAngularTerm_integral_abs_le haxi hu hχ hχs hρU hρ1 htmem (hW t ht)
  have hangle : -(∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
      * curlComp u 1 (meridional (polarR x) (x 2), t)))
      ≤ (1 / 4) * cutoffEnstrophyDissipation χ u t + 4 * W t ^ 2 * cutoffEnstrophy χ u t :=
    le_trans (neg_le_abs _) hang
  have hb := (hbal t ht).2
  refine closure_energy_arith C Cm (G t) (W t ^ 2) (cutoffEnstrophy χ u t)
    (cutoffEnstrophyDissipation χ u t) (deriv (cutoffEnstrophy χ u) t)
    (cutoffStretching χ u t) (∫ x : Vec3, χ x ^ 2 * stretchGTerm u x t) (Mix t)
    (∫ x : Vec3, χ x ^ 2 * (2 * stretchAngularSwirl u x t
      * curlComp u 1 (meridional (polarR x) (x 2), t)))
    hC0 hCm (hGnn t) (sq_nonneg _) hYnn hb (hsplit t ht) ?_ hangle (hmix t ht)
  linarith only [hstretch]

end CIV
