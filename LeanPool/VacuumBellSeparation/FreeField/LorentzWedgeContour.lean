/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpacetimeSpatialTranslation
public import LeanPool.VacuumBellSeparation.FreeField.LorentzSourceWave
public import LeanPool.VacuumBellSeparation.FreeField.ShiftedWedgeContour

/-!
# Literal compact-source contours for shifted and Lorentz-transformed wedges

Spatial translation first gives the exact damping for an original
spacetime test. Actual Lorentz unitarity and the entire-wave identity then
give the original Cauchy-data contour at Lambda b_phi(p). The operator here
is explicitly the unitary transport of the proved full shifted-wedge
power; the generic transformed spacetime graph identification is separate.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

theorem wedgeWave_spatialTranslate_edge_norm_sq (m ℓ θ : ℝ)
    (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖wedgeWave m (spacetimeSpatialTranslate (-(ℓ • e₁)) F)
      ((θ : ℂ) * Complex.I) p‖ ^ 2 =
      Real.exp (-2 * ℓ * dispersion m p * Real.sin θ) *
        ‖wedgeWave m F ((θ : ℂ) * Complex.I) p‖ ^ 2 := by
  rw [wedgeWave_spatialTranslate, norm_mul, mul_pow, norm_complexTranslation_edge,
    pow_two, ← Real.exp_add]
  congr 2
  ring

theorem spacetime_shiftedWedge_contour_norm {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge ℓ)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (oneParticleL2 hm F, χ) ∈ (shiftedWedgeExponential hm ℓ c).graph ∧
      ‖χ‖ ^ 2 = ∫ p, Real.exp (-2 * ℓ * dispersion m p * Real.sin (2 * Real.pi * c)) *
        ‖wedgeWave m F (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p‖ ^ 2
        ∂oneParticleMeasure m := by
  let G := spacetimeSpatialTranslate (-(ℓ • e₁)) F
  have hG := spacetimeSpatialTranslate_support_wedge_zero ℓ F hF
  let ζ : ℂ := ((2 * Real.pi * c : ℝ) : ℂ) * Complex.I
  have hζ := wedgeWave_angle_mem_strip hc hc2
  let ψ := wedgeWaveL2 hm G hG ζ hζ
  refine ⟨oneParticleSpatialTranslation m (ℓ • e₁) ψ, ?_, ?_⟩
  · rw [shiftedWedgeExponential, unitaryPartialTransport_mem_graph,
      LinearIsometryEquiv.symm_apply_apply, oneParticleSpatialTranslation_symm,
      ← oneParticleL2_spatialTranslate]
    exact wedgeWave_mem_physicalRapidityPower_graph hm G hG hc hc2
  · rw [LinearIsometryEquiv.norm_map, norm_L2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [wedgeWaveL2_ae hm G hG ζ hζ] with p hp
    exact (congrArg (fun z : ℂ => ‖z‖ ^ 2) hp).trans
      (wedgeWave_spatialTranslate_edge_norm_sq m ℓ (2 * Real.pi * c) F p)

theorem tsupport_compLorentz_subset_wedge (Λ : Spacetime ≃L[ℝ] Spacetime)
    (ℓ : ℝ) (F : RealTestFunction) (hF : tsupport F.1 ⊆ Λ '' leftWedge ℓ) :
    tsupport (F.compCLE Λ).1 ⊆ leftWedge ℓ := by
  rw [RealTestFunction.tsupport_compCLE]
  intro x hx
  obtain ⟨y, hy, he⟩ := hF hx
  exact (Λ.injective he) ▸ hy

theorem timeZero_lorentzWedge_contour_norm {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (hfuture : IsOrthochronousMap Λ)
    (F : RealTestFunction) (u : TimeZeroSource) (heq : oneParticleL2 hm F = timeZeroL2 hm u)
    (hF : tsupport F.1 ⊆ Λ '' leftWedge ℓ)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (timeZeroL2 hm u, χ) ∈
        (unitaryPartialTransport (oneParticleLorentz hm Λ hΛ hfuture)
          (shiftedWedgeExponential hm ℓ c)).graph ∧
      ‖χ‖ ^ 2 = ∫ p, Real.exp (-2 * ℓ * dispersion m p * Real.sin (2 * Real.pi * c)) *
        ‖complexSourceWave u (complexifiedSpacetimeMap Λ
          (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p))‖ ^ 2
        ∂oneParticleMeasure m := by
  obtain ⟨ψ, hψ, hnorm⟩ := spacetime_shiftedWedge_contour_norm hm ℓ (F.compCLE Λ)
    (tsupport_compLorentz_subset_wedge Λ ℓ F hF) hc hc2
  have hsource : (oneParticleLorentz hm Λ hΛ hfuture).symm (timeZeroL2 hm u) =
      oneParticleL2 hm (F.compCLE Λ) := by
    apply (oneParticleLorentz hm Λ hΛ hfuture).injective
    rw [LinearIsometryEquiv.apply_symm_apply, oneParticleLorentz_oneParticleL2,
      RealTestFunction.compCLE_compCLE_symm, heq]
  refine ⟨oneParticleLorentz hm Λ hΛ hfuture ψ, ?_, ?_⟩
  · rw [unitaryPartialTransport_mem_graph, LinearIsometryEquiv.symm_apply_apply, hsource]
    exact hψ
  · rw [LinearIsometryEquiv.norm_map, hnorm]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by
      dsimp only
      rw [wedgeWave_compLorentz_eq_complexSourceWave hm Λ hΛ hfuture F u heq]

end VacuumBellSeparation
