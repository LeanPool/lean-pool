/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffFinal
public import LeanPool.CIVAxisymmetric.Zoom.MeridionalContradictionDichotomy
public import LeanPool.CIVAxisymmetric.Zoom.FiniteSelectionBound

/-!
# The finite-axis contradiction at the selected points

The last paragraph of Step 2 of the proof of `prop:aniso:small`: in the finite-axis case
(`r_n / λ_n ≤ A`), the points selected in `eq:aniso:zoom:selected` have zoomed coordinates
`(r_n / λ_n, 0, -1)` about the moving axis point `(0, z_n)`, and the endpoint vanishing of the
rescaled potential vorticity (`eq:aniso:zoom:finite:endpoint`, through
`CIV.false_of_finiteZoomCutoff_raw_selection`) contradicts the lower bound `c₀`. The selected
data are exactly those returned by the finite-axis branch of
`CIV.exists_seq_three_terms_dichotomy`, with `λ_n = √(-t_n)`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The finite-axis branch of the selection of `eq:aniso:zoom:selected` is contradictory once
the rescaled potential vorticity about the moving axis points `(0, x₃ n)`, at scale
`λ_n = √(-t_n)`, tends to zero at every point of `{τ = -1}` off the axis. -/
theorem false_of_real_finite_selection {C h ρ : ℝ} (hC : 0 ≤ C) (hh0 : 0 < h) (hh1 : h < 1 / 2)
    (hρ : ρ < 1) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {c₀ : ℝ} (hc₀ : 0 < c₀) {t x₁ x₃ : ℕ → ℝ} (hx₁ : ∀ n, 0 ≤ x₁ n)
    (htlim : Tendsto t atTop (nhds 0))
    (hmem : ∀ n, meridional (x₁ n) (x₃ n) ∈ vec3Ball (0 : Vec3) ρ)
    (htmem : ∀ n, t n ∈ Set.Ioo (-1 : ℝ) 0)
    (hineq : ∀ n, c₀ < (-(t n)) *
        (|spatialPartial (fun w => u w 0) 0 (meridional (x₁ n) (x₃ n), t n)| +
          |radialQuotient u (meridional (x₁ n) (x₃ n), t n)| +
          |spatialPartial (fun w => u w 2) 2 (meridional (x₁ n) (x₃ n), t n)|))
    {A : ℝ} (hA : ∀ n, x₁ n / Real.sqrt (-(t n)) ≤ A)
    (hΩ0 : ∀ q : ℝ × ℝ, 0 < q.1 →
      Tendsto (fun n => zoomOmega (Real.sqrt (-(t n))) h (x₃ n) u (q, -1)) atTop (nhds 0)) :
    False := by
  set lam : ℕ → ℝ := fun n => Real.sqrt (-(t n)) with hlam_def
  have hlam0 : ∀ n, 0 < lam n := fun n => Real.sqrt_pos.mpr (by linarith only [(htmem n).2])
  have hlam1 : ∀ n, lam n < 1 := fun n => by
    rw [hlam_def, Real.sqrt_lt' one_pos]; linarith only [(htmem n).1]
  have hlamT : Tendsto lam atTop (nhds 0) := by
    have : Tendsto (fun n => Real.sqrt (-(t n))) atTop (nhds (Real.sqrt (-0))) :=
      (htlim.neg).sqrt
    simpa using this
  have hzc : ∀ n, |x₃ n| ≤ ρ := fun n => by
    obtain ⟨hs, hρpos⟩ := (meridional_mem_vec3Ball_zero_iff _ _ _).mp (hmem n)
    have h3 : x₃ n ^ 2 < ρ ^ 2 := by nlinarith only [hs, sq_nonneg (x₁ n)]
    exact (abs_lt_of_sq_lt_sq h3 hρpos.le).le
  set Rsel : ℕ → ℝ := fun n => x₁ n / lam n with hRsel
  have hRmem : ∀ n, Rsel n ∈ Icc (0 : ℝ) (max A 1) := fun n =>
    ⟨div_nonneg (hx₁ n) (hlam0 n).le, le_trans (hA n) (le_max_left _ _)⟩
  refine false_of_finiteZoomCutoff_raw_selection hC hh0 hh1 hzc hρ hb hsol haxi hlam0 hlam1 hlamT
    hΩ0 (lt_of_lt_of_le one_pos (le_max_right A 1)) hc₀ hRmem (fun n => ?_)
  have ht : t n < 0 := (htmem n).2
  have hR0 : 0 ≤ Rsel n := (hRmem n).1
  have hmul : lam n * Rsel n = x₁ n := by
    rw [hRsel]; field_simp [(hlam0 n).ne']
  have hp : zoomPoint (Real.sqrt (-(t n))) h (x₃ n) ((Rsel n, 0), (-1 : ℝ)) ∈ unitCylinder := by
    have hsq : Real.sqrt (-(t n)) ^ 2 = -(t n) := Real.sq_sqrt (by linarith only [ht])
    have hz : zoomPoint (Real.sqrt (-(t n))) h (x₃ n) ((Rsel n, 0), (-1 : ℝ))
        = (meridional (x₁ n) (x₃ n), t n) := by
      simp only [zoomPoint, mul_zero, add_zero, hsq]
      rw [show Real.sqrt (-(t n)) * Rsel n = x₁ n from hmul]
      rw [show -(t n) * -1 = t n by ring]
    rw [hz]
    obtain ⟨hs, hρpos⟩ := (meridional_mem_vec3Ball_zero_iff _ _ _).mp (hmem n)
    refine ⟨?_, htmem n⟩
    rw [meridional_mem_vec3Ball_zero_iff]
    exact ⟨by nlinarith only [hs, hρ, hρpos], one_pos⟩
  have hi := hineq n
  rw [← hmul] at hi
  exact (lt_of_neg_t_mul_meridionalQuantity_selection_lt_sqrt (hu.of_le (by simp)) ht hR0 hp hi).le

end CIV
