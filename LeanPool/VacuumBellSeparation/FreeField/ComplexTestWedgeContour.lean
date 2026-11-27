/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LorentzContainingWedge

/-!
# Exact Lorentz contours for complexified compact test sources

The complex source is the literal sum of a real test pair and i times
another real test pair. Linearity of the full maximal graph gives the
contour including cross terms, without an extra norm-loss factor.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

/-- Wedge contour phase. -/
noncomputable def wedgeContourPhase (m ℓ θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (-(Complex.I * spatialDot
    (complexShellBoost m ((θ : ℂ) * Complex.I) p).2
    (fun i => ((-(ℓ • e₁)) i : ℂ))))

theorem norm_wedgeContourPhase_sq (m ℓ θ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖wedgeContourPhase m ℓ θ p‖ ^ 2 =
      Real.exp (-2 * ℓ * dispersion m p * Real.sin θ) := by
  rw [wedgeContourPhase, norm_complexTranslation_edge, pow_two, ← Real.exp_add]
  congr 1
  ring

variable {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
  (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
  (hfuture : IsOrthochronousMap Λ)

/-- Linear isometry equivalence for the lorentz wedge contour unitary, of type `Lp ℂ 2
(oneParticleMeasure m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def lorentzWedgeContourUnitary :
    Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  (oneParticleSpatialTranslation m (ℓ • e₁)).trans (oneParticleLorentz hm Λ hΛ hfuture)

theorem timeZero_lorentzWedge_graph_ae
    (F : RealTestFunction) (u : TimeZeroSource) (heq : oneParticleL2 hm F = timeZeroL2 hm u)
    (hF : tsupport F.1 ⊆ Λ '' leftWedge ℓ)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (timeZeroL2 hm u, χ) ∈
        (unitaryPartialTransport (oneParticleLorentz hm Λ hΛ hfuture)
          (shiftedWedgeExponential hm ℓ c)).graph ∧
      (lorentzWedgeContourUnitary hm ℓ Λ hΛ hfuture).symm χ =ᵐ[oneParticleMeasure m]
        fun p => wedgeContourPhase m ℓ (2 * Real.pi * c) p *
          complexSourceWave u (complexifiedSpacetimeMap Λ
            (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)) := by
  let G := spacetimeSpatialTranslate (-(ℓ • e₁)) (F.compCLE Λ)
  have hG : tsupport G.1 ⊆ leftWedge 0 := spacetimeSpatialTranslate_support_wedge_zero ℓ
    (F.compCLE Λ) (tsupport_compLorentz_subset_wedge Λ ℓ F hF)
  let ζ : ℂ := ((2 * Real.pi * c : ℝ) : ℂ) * Complex.I
  have hζ := wedgeWave_angle_mem_strip hc hc2
  let ψ := wedgeWaveL2 hm G hG ζ hζ
  refine ⟨lorentzWedgeContourUnitary hm ℓ Λ hΛ hfuture ψ, ?_, ?_⟩
  · rw [lorentzWedgeContourUnitary, LinearIsometryEquiv.trans_apply,
      unitaryPartialTransport_mem_graph, LinearIsometryEquiv.symm_apply_apply,
      ← heq, oneParticleLorentz_symm_oneParticleL2,
      shiftedWedgeExponential, unitaryPartialTransport_mem_graph,
      LinearIsometryEquiv.symm_apply_apply, oneParticleSpatialTranslation_symm,
      ← oneParticleL2_spatialTranslate]
    exact wedgeWave_mem_physicalRapidityPower_graph hm G hG hc hc2
  · rw [LinearIsometryEquiv.symm_apply_apply]
    filter_upwards [wedgeWaveL2_ae hm G hG ζ hζ] with p hp
    rw [hp]
    change wedgeWave m (spacetimeSpatialTranslate (-(ℓ • e₁)) (F.compCLE Λ)) ζ p = _
    rw [wedgeWave_spatialTranslate,
      wedgeWave_compLorentz_eq_complexSourceWave hm Λ hΛ hfuture F u heq]
    rfl

variable {U : Set (EuclideanSpace ℝ (Fin 3))} {R : ℝ}
  (hR : 0 < R) (hU : U ⊆ Metric.ball 0 R)
  (hregion : doubleCone (0, (0 : EuclideanSpace ℝ (Fin 3))) R ⊆ Λ '' leftWedge ℓ)

include hR hU hregion in
theorem complexTest_lorentzWedge_contour_norm
    (u v : SourceTestSpace hm U) {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (timeZeroL2 hm u.1 + Complex.I • timeZeroL2 hm v.1, χ) ∈
        (unitaryPartialTransport (oneParticleLorentz hm Λ hΛ hfuture)
          (shiftedWedgeExponential hm ℓ c)).graph ∧
      ‖χ‖ ^ 2 = ∫ p, Real.exp (-2 * ℓ * dispersion m p * Real.sin (2 * Real.pi * c)) *
        ‖complexSourceWave u.1 (complexifiedSpacetimeMap Λ
          (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)) +
          Complex.I * complexSourceWave v.1 (complexifiedSpacetimeMap Λ
          (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p))‖ ^ 2
        ∂oneParticleMeasure m := by
  obtain ⟨F, hF, hFu⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hR 0 u.1
    (u.2.1.trans hU) (u.2.2.trans hU)
  obtain ⟨G, hG, hGv⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hR 0 v.1
    (v.2.1.trans hU) (v.2.2.trans hU)
  obtain ⟨χ, hχ, haeχ⟩ := timeZero_lorentzWedge_graph_ae hm ℓ Λ hΛ hfuture
    F u.1 hFu (hF.trans hregion) hc hc2
  obtain ⟨ψ, hψ, haeψ⟩ := timeZero_lorentzWedge_graph_ae hm ℓ Λ hΛ hfuture
    G v.1 hGv (hG.trans hregion) hc hc2
  let A := unitaryPartialTransport (oneParticleLorentz hm Λ hΛ hfuture)
    (shiftedWedgeExponential hm ℓ c)
  let V := lorentzWedgeContourUnitary hm ℓ Λ hΛ hfuture
  refine ⟨χ + Complex.I • ψ, ?_, ?_⟩
  · exact A.graph.add_mem hχ (A.graph.smul_mem Complex.I hψ)
  · rw [← V.symm.norm_map (χ + Complex.I • ψ), map_add, map_smul,
      norm_L2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [haeχ, haeψ, Lp.coeFn_add (V.symm χ) (Complex.I • V.symm ψ),
      Lp.coeFn_smul Complex.I (V.symm ψ)] with p hχp hψp hadd hsmul
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply]
    rw [hχp, hψp]
    simp only [smul_eq_mul]
    rw [show wedgeContourPhase m ℓ (2 * Real.pi * c) p *
        complexSourceWave u.1 (complexifiedSpacetimeMap Λ
          (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)) +
        Complex.I * (wedgeContourPhase m ℓ (2 * Real.pi * c) p *
        complexSourceWave v.1 (complexifiedSpacetimeMap Λ
          (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p))) =
        wedgeContourPhase m ℓ (2 * Real.pi * c) p *
        (complexSourceWave u.1 (complexifiedSpacetimeMap Λ
          (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)) +
        Complex.I * complexSourceWave v.1 (complexifiedSpacetimeMap Λ
          (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p))) by ring,
      norm_mul, mul_pow, norm_wedgeContourPhase_sq]

include hΛ hfuture hR hU hregion in
/-- Exact complex-source estimate retaining all cross terms. -/
theorem complexTest_lorentzContour_le_sourceWeight
    (u v : SourceTestSpace hm U) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (∫ p, Real.exp (-2 * ℓ * dispersion m p * Real.sin (2 * Real.pi * c)) *
      ‖complexSourceWave u.1 (complexifiedSpacetimeMap Λ
        (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)) +
        Complex.I * complexSourceWave v.1 (complexifiedSpacetimeMap Λ
        (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p))‖ ^ 2
      ∂oneParticleMeasure m) ≤
      ‖sourceModularWeight hm U c
        (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
          Complex.I • Gaussian.HilbertComplexification.ofReal (v : SourceHilbert hm U))‖ ^ 2 := by
  obtain ⟨χ, hχ, hnorm⟩ := complexTest_lorentzWedge_contour_norm hm ℓ Λ hΛ hfuture
    hR hU hregion u v hc.le hc2
  obtain ⟨ψ, hψ, hbound⟩ := lorentzWedgeExponential_containing_ball hm ℓ Λ hΛ hfuture
    hR hU hregion hc hc2
    (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
      Complex.I • Gaussian.HilbertComplexification.ofReal (v : SourceHilbert hm U))
  rw [map_add, map_smul, complexSourceMap_ofReal_test, complexSourceMap_ofReal_test] at hψ
  have he := (unitaryPartialTransport (oneParticleLorentz hm Λ hΛ hfuture)
    (shiftedWedgeExponential hm ℓ c)).mem_graph_snd_inj hχ hψ rfl
  rw [← hnorm, he]
  exact pow_le_pow_left₀ (norm_nonneg _) hbound 2

end VacuumBellSeparation
