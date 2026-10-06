/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ZoomLimitEndpoint
public import LeanPool.CIVAxisymmetric.Zoom.FiniteDriftExtraction
-- the modules of the drift extraction, the limit passage, the receding inputs and the finite
-- residual (set to their paths):
public import LeanPool.CIVAxisymmetric.Zoom.DriftExtraction
public import LeanPool.CIVAxisymmetric.Zoom.DriftLimitEquation
public import LeanPool.CIVAxisymmetric.Zoom.RecedingLimitInputs
public import LeanPool.CIVAxisymmetric.Zoom.RecedingResidual
public import LeanPool.CIVAxisymmetric.Zoom.FiniteResidual

/-!
# The two limit equations of the proof of `prop:aniso:small`

The locally uniform limits of the rescaled vorticities solve, in the sense of distributions and
with an admissible drift, the limit equations of Steps 2 and 3:
`eq:aniso:zoom:finite:limit` on `ℝ⁴ × ℝ × (-∞, -1)` (the lifted potential vorticity,
`(m, d) = (5, 4)`) and `eq:aniso:zoom:receding:limit:a` on `ℝ² × (-∞, -1)` (the azimuthal
vorticity, `(m, d) = (2, 1)`). The drift is extracted from the rescaled drifts and the finite-`n`
equations are passed to the limit.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- Locally uniform convergence on `(ℝ × ℝ) × (-∞, -1]` pulled back to `Vec 2 × ℝ`. -/
theorem tendstoUniformlyOn_planeLift {Θn : ℕ → (ℝ × ℝ) × ℝ → ℝ} {Θ : (ℝ × ℝ) × ℝ → ℝ}
    (hconv : ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K → K ⊆ {p : (ℝ × ℝ) × ℝ | p.2 ≤ -1} →
      TendstoUniformlyOn Θn Θ atTop K) :
    ∀ K : Set (Vec 2 × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic (-1) →
      TendstoUniformlyOn (fun n z => Θn n (planeLiftPoint z)) (fun z => Θ (planeLiftPoint z))
        atTop K := by
  intro K hK hKs
  have hK' : IsCompact (planeLiftPoint '' K) := hK.image continuous_planeLiftPoint
  have hsub : planeLiftPoint '' K ⊆ {p : (ℝ × ℝ) × ℝ | p.2 ≤ -1} := by
    rintro _ ⟨z, hz, rfl⟩; exact (hKs hz).2
  exact ((hconv _ hK' hsub).comp planeLiftPoint).mono (fun z hz => mem_image_of_mem _ hz)

/-- `eq:aniso:zoom:receding:limit:a`: the locally uniform limit of the rescaled azimuthal
vorticities at the moving centres solves the limit equation on `ℝ² × (-∞, -1)` in the sense of
distributions, with an admissible drift. -/
theorem exists_admissibleDrift_zoomThetaLimit {C h CΓ ρ Rstar tstar : ℝ}
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {lam rc zc : ℕ → ℝ}
    (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1)
    (htstar : tstar < 0) (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) (hC : 0 ≤ C)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f) (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (hA : Tendsto (fun n => rc n / lam n) atTop atTop)
    (Θ : (ℝ × ℝ) × ℝ → ℝ) (hΘc : ContinuousOn Θ {p : (ℝ × ℝ) × ℝ | p.2 ≤ -1})
    (hconv : ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K → K ⊆ {p : (ℝ × ℝ) × ℝ | p.2 ≤ -1} →
      TendstoUniformlyOn (fun n => zoomTheta (lam n) h (rc n) (zc n) u) Θ atTop K) :
    ∃ (B : Vec 2 × ℝ → Vec 2) (divB : Vec 2 × ℝ → ℝ),
      IsAdmissibleDrift 2 (Iio (-1)) B divB ∧
      IsDistributionalDriftDiffusion 2 1 (Iio (-1)) B divB (fun z => Θ (planeLiftPoint z)) := by
  obtain ⟨hc, hbd, hdiv⟩ := recDrift_extraction_hypotheses hh hρ0 hρR hR1 hcz hC hb
    hu hsol haxi hlam_pos hlam_lim hA
  obtain ⟨φ, hφ, B, divB, hB, hweak⟩ := exists_subseq_admissibleDrift
    (fun n => recDrift (lam n) h (rc n) (zc n) u) (fun n => recDriftDiv (lam n) h (rc n) (zc n) u)
    hc hbd hdiv
  refine ⟨B, divB, hB, ?_⟩
  have hφt := hφ.tendsto_atTop
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρR hR1
  have hL1 := tendsto_lintegral_of_tendstoUniformlyOn (T := -1) _ _
    (tendstoUniformlyOn_planeLift hconv)
  have hq : IsLocallyBoundedOn 2 (Iio (-1)) (fun z => Θ (planeLiftPoint z)) := by
    have hbnd : ∀ z : Vec 2 × ℝ, z.2 ≤ -1 → |Θ (planeLiftPoint z)| ≤ C := by
      intro z hz
      have hpt := (hconv {planeLiftPoint z} isCompact_singleton
        (fun x hx => by rw [mem_singleton_iff.mp hx]; exact hz)).tendsto_at (mem_singleton _)
      have h1 := abs_le_of_tendsto_zoomTheta hh hρ0 hρ1 hb hu hcz hlam_pos hlam_lim
        (p := planeLiftPoint z) (by show z.2 < 0; linarith only [hz]) hpt
      have hτ1 : (1 : ℝ) ≤ -(planeLiftPoint z).2 := by show (1 : ℝ) ≤ -z.2; linarith only [hz]
      have hr : (-(planeLiftPoint z).2) ^ (-1 - h) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by linarith only [hh.1])
      exact h1.trans (mul_le_of_le_one_right hC hr)
    have hcont : ContinuousOn (fun z : Vec 2 × ℝ => Θ (planeLiftPoint z)) (univ ×ˢ Iio (-1)) :=
      hΘc.comp continuous_planeLiftPoint.continuousOn
        (fun z hz => show z.2 ≤ -1 from le_of_lt hz.2)
    refine ⟨hcont.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Iio), ?_⟩
    intro J hJ hJsub
    refine ⟨C, ?_⟩
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod hJ.measurableSet)] with z hzJ
    exact hbnd z (le_of_lt (hJsub hzJ.2))
  refine isDistributionalDriftDiffusion_of_tendsto
    (fun n z => zoomTheta (lam (φ n)) h (rc (φ n)) (zc (φ n)) u (planeLiftPoint z)) _
    (fun n => recDrift (lam (φ n)) h (rc (φ n)) (zc (φ n)) u)
    (fun n => recDriftDiv (lam (φ n)) h (rc (φ n)) (zc (φ n)) u) B divB hB hweak hq ?_ ?_ ?_
  · intro K hK hKs
    obtain ⟨M, hM⟩ := recDrift_bounds hh hρ0 hρR hR1 hcz hC hb hu
      hlam_pos hlam_lim hA K hK hKs
    exact ⟨M, hφt.eventually hM⟩
  · intro K hK hKs
    exact (hL1 K hK hKs).comp hφt
  · intro ψ hψ
    exact (tendsto_recResidual hh hρ0 hρR hR1 htstar hcz hC hb hu hsol haxi hΓ hforce hlam_pos
      hlam_lim hA ψ hψ).comp hφt

/-- `eq:aniso:zoom:finite:limit`: the locally uniform limit of the rescaled potential vorticities
at the moving axis points, lifted to `ℝ⁴ × ℝ`, solves the limit equation on `ℝ⁵ × (-∞, -1)` in
the sense of distributions, with an admissible drift. -/
theorem exists_admissibleDrift_zoomOmegaLimit {C h CΓ ρ Rstar tstar : ℝ}
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {lam zc : ℕ → ℝ}
    (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1)
    (htstar : tstar < 0) (hzc : ∀ n, |zc n| ≤ ρ) (hC : 0 ≤ C)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f) (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (Ω : (ℝ × ℝ) × ℝ → ℝ) (hΩc : ContinuousOn Ω {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ p.2 ≤ -1})
    (hconv : ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K →
      K ⊆ {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ p.2 ≤ -1} →
      TendstoUniformlyOn (fun n => zoomOmega (lam n) h (zc n) u) Ω atTop K) :
    ∃ (B : Vec 5 × ℝ → Vec 5) (divB : Vec 5 × ℝ → ℝ),
      IsAdmissibleDrift 5 (Iio (-1)) B divB ∧
      IsDistributionalDriftDiffusion 5 4 (Iio (-1)) B divB (fun z => Ω (zoomLiftPoint z)) := by
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρR hR1
  obtain ⟨hc, hbd, hdiv⟩ := finDrift_extraction_hypotheses hh hρ0 hρ1 hC hb hsol haxi hzc
    hlam_lim
  obtain ⟨φ, hφ, B, divB, hB, hweak⟩ := exists_subseq_admissibleDrift
    (fun n => zoomDrift (lam n) h (zc n) u) (fun n => finDriftDiv (lam n) h (zc n) u)
    hc hbd hdiv
  refine ⟨B, divB, hB, ?_⟩
  have hφt := hφ.tendsto_atTop
  refine isDistributionalDriftDiffusion_of_tendsto
    (fun n => zoomOmegaLift (lam (φ n)) h (zc (φ n)) u) _
    (fun n => zoomDrift (lam (φ n)) h (zc (φ n)) u)
    (fun n => finDriftDiv (lam (φ n)) h (zc (φ n)) u) B divB hB hweak
    (isLocallyBoundedOn_zoomOmegaLimit hh hρ0 hρ1 hb hu haxi hzc hlam_pos hlam_lim Ω hΩc hconv)
    ?_ ?_ ?_
  · intro K hK hKs
    obtain ⟨M, hM⟩ := finDrift_bounds hh hρ0 hρ1 hC hb hu haxi hzc hlam_lim K hK hKs
    exact ⟨M, hφt.eventually hM⟩
  · intro K hK hKs
    exact (tendsto_lintegral_zoomOmegaLift hh hρ0 hρ1 hC hb hu haxi hzc hlam_pos hlam_lim Ω hconv
      K hK hKs).comp hφt
  · intro ψ hψ
    exact (tendsto_finResidual hh hρ0 hρR hR1 htstar hzc hC hb hu hsol haxi hfaxi hΓ hforce
      hlam_lim ψ hψ).comp hφt

end CIV
