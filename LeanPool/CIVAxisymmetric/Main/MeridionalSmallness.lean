/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Zoom.ZoomStandingData
public import LeanPool.CIVAxisymmetric.Zoom.ZoomLimitEquations
public import LeanPool.CIVAxisymmetric.Zoom.FiniteRealSelection
public import LeanPool.CIVAxisymmetric.Zoom.RecedingRealSelection
public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisCompactness
public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallness
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution

/-!
# The public statement `CIV.Main.meridionalSmallness`

This module proves the statement `CIV.meridionalSmallness` (`prop:aniso:small`). The proof is the
zoom argument of Section `sec:aniso:zoom`. Assume `eq:aniso:small` fails at a radius `ρ`. The
selection `eq:aniso:zoom:selected` and the finite/receding dichotomy
(`CIV.exists_seq_three_terms_dichotomy`) give times `t_n ↑ 0` and points `(x₁ n, x₃ n)`. With the
angle-averaged classical system and the circulation bound `eq:aniso:zoom:circulation`
(`CIV.exists_zoom_standing_data`), each branch runs four steps:
- compactness;
- the limit equation;
- the comparison principle `lem:aniso:comparison`;
- the endpoint argument.

The last step contradicts the selection.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of `prop:aniso:small`: under the hypotheses of `thm:aniso:main`, for
every `0 < ρ < 1`, `(-t) G_ρ(t) → 0` as `t ↑ 0` (`eq:aniso:small`). -/
theorem meridionalSmallness (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (h : ℝ) (hh : 0 < h ∧ h < 1 / 2) (hMf : ForceC2Bounded f)
    (C : ℝ) (hC : 0 < C) (hbounds : AnisotropicBounds C h u) :
    ∀ ρ ∈ Ioo (0 : ℝ) 1, MeridionalSmallness ρ u := by
  intro ρ hρ
  by_contra hnot
  obtain ⟨hcl, hfaxi, hMf', Rstar, tstar, CΓ, hρR, hR1, htstar, hCΓ, hΓ⟩ :=
    exists_zoom_standing_data q u Du p f hsol henergy hu hp hf haxi hMf hρ
  obtain ⟨c₀, hc₀, t, x₁, x₃, hx₁, -, htlim, hmem, htmem, hineq, hdich⟩ :=
    exists_seq_three_terms_dichotomy hu haxi hbounds hh.1 hρ.2.le hnot
  set lam : ℕ → ℝ := fun n => Real.sqrt (-(t n)) with hlam_def
  have hlam_pos : ∀ n, 0 < lam n := fun n => Real.sqrt_pos.mpr (by linarith only [(htmem n).2])
  have hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hlam_pos⟩
    have : Tendsto (fun n => Real.sqrt (-(t n))) atTop (nhds (Real.sqrt (-0))) :=
      (htlim.neg).sqrt
    simpa using this
  have hcz : ∀ n, x₁ n ^ 2 + x₃ n ^ 2 ≤ ρ ^ 2 := fun n =>
    ((meridional_mem_vec3Ball_zero_iff _ _ _).mp (hmem n)).1.le
  have hzc : ∀ n, |x₃ n| ≤ ρ := fun n => by
    have h3 : x₃ n ^ 2 ≤ ρ ^ 2 := by nlinarith only [hcz n, sq_nonneg (x₁ n)]
    exact abs_le.mpr (abs_le_of_sq_le_sq' h3 hρ.1.le)
  have hsub : ∀ {φ : ℕ → ℕ}, StrictMono φ → Tendsto (fun n => t (φ n)) atTop (nhds 0) :=
    fun hφ => htlim.comp hφ.tendsto_atTop
  rcases hdich with ⟨A, hA⟩ | hA
  · -- the finite-axis branch
    obtain ⟨φ, hφ, Ω, hΩc, hconv⟩ := exists_subseq_tendstoUniformlyOn_zoomOmega_moving hh
      hρ.1.le hρR hR1.le htstar.2 hzc hC.le hCΓ hbounds hu hcl haxi hΓ hMf' lam hlam_pos
      hlam_lim
    have hlamφ : Tendsto (fun n => lam (φ n)) atTop (nhdsWithin 0 (Ioi 0)) :=
      hlam_lim.comp hφ.tendsto_atTop
    obtain ⟨B, divB, hB, heq⟩ := exists_admissibleDrift_zoomOmegaLimit hh hρ.1.le hρR hR1.le
      htstar.2 (fun n => hzc (φ n)) hC.le hbounds hu hcl haxi hfaxi hΓ hMf'
      (fun n => hlam_pos (φ n)) hlamφ Ω hΩc hconv
    have hΩ0 := tendsto_zoomOmega_endpoint_of_limit hh hρ.1.le hρ.2 hbounds hu haxi
      (fun n => hzc (φ n)) (fun n => hlam_pos (φ n)) hlamφ Ω hΩc hconv B divB hB heq
    exact false_of_real_finite_selection hC.le hh.1 hh.2 hρ.2 hu hbounds hcl haxi hc₀
      (fun n => hx₁ (φ n)) (hsub hφ) (fun n => hmem (φ n)) (fun n => htmem (φ n))
      (fun n => hineq (φ n)) (fun n => hA (φ n)) hΩ0
  · -- the receding-axis branch
    obtain ⟨φ, hφ, Θ, hΘc, hconv⟩ := exists_subseq_tendstoUniformlyOn_zoomTheta_moving hh
      hρ.1.le hρR hR1.le htstar.2 hcz hC.le hCΓ hbounds hu hcl haxi hΓ hMf' lam hlam_pos
      hlam_lim hA
    have hlamφ : Tendsto (fun n => lam (φ n)) atTop (nhdsWithin 0 (Ioi 0)) :=
      hlam_lim.comp hφ.tendsto_atTop
    have hAφ : Tendsto (fun n => x₁ (φ n) / lam (φ n)) atTop atTop :=
      hA.comp hφ.tendsto_atTop
    obtain ⟨B, divB, hB, heq⟩ := exists_admissibleDrift_zoomThetaLimit hh hρ.1.le hρR hR1.le
      htstar.2 (fun n => hcz (φ n)) hC.le hbounds hu hcl haxi hΓ hMf'
      (fun n => hlam_pos (φ n)) hlamφ hAφ Θ hΘc hconv
    have hΘ0 := tendsto_zoomTheta_endpoint_of_limit hh hρ.1.le hρ.2 hbounds hu
      (fun n => hcz (φ n)) (fun n => hlam_pos (φ n)) hlamφ Θ hΘc hconv B divB hB heq
    exact false_of_real_receding_selection hC.le hh.1 hh.2 hρ.2 hu hbounds hcl haxi hc₀
      (hsub hφ) (fun n => hmem (φ n)) (fun n => htmem (φ n)) (fun n => hineq (φ n)) hAφ hΘ0

end Main
end CIV
