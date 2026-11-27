/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceTranslation
public import LeanPool.VacuumBellSeparation.FreeField.AntilinearGraphTransport
public import LeanPool.VacuumBellSeparation.FreeField.WedgePhysicalResolvent

/-!
# The full physical modular graph and resolvent of each shifted wedge

The source graph is the literal graph of the translated completed source
space. Its universal S*S is proved equal to the unitary translate of the
maximal rapidity exponential. The original kappa kappa*/2 resolvent then
has the exact logistic multiplier in shifted Fourier coordinates.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m) (ℓ : ℝ)

/-- Linear isometry equivalence for the shifted wedge Fourier, of type `Lp ℂ 2 (oneParticleMeasure
m) ≃ₗᵢ[ℂ] RapidityL2`. -/
noncomputable def shiftedWedgeFourier : Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] RapidityL2 :=
  (oneParticleSpatialTranslation m (ℓ • e₁)).symm.trans (oneParticleRapidityFourier hm)

/-- Linear map for the shifted wedge exponential, of type `Lp ℂ 2 (oneParticleMeasure m) →ₗ.[ℂ] Lp
ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def shiftedWedgeExponential (c : ℝ) :
    Lp ℂ 2 (oneParticleMeasure m) →ₗ.[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  unitaryPartialTransport (oneParticleSpatialTranslation m (ℓ • e₁))
    (physicalRapidityExponential hm c)

theorem shiftedWedgeExponential_mem_graph (c : ℝ)
    (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    (ψ, χ) ∈ (shiftedWedgeExponential hm ℓ c).graph ↔
      (shiftedWedgeFourier hm ℓ ψ, shiftedWedgeFourier hm ℓ χ) ∈
        (rapidityExponential c).graph := by
  rw [shiftedWedgeExponential, unitaryPartialTransport_mem_graph,
    physicalRapidityExponential_mem_graph_iff]
  rfl

/-- Literal full S*S identification, for every real edge position. -/
theorem shiftedWedgeTomitaModularGraph_iff (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    (ψ, χ) ∈ antilinearGraphSquare (sourceTomitaGraph hm (leftWedgeTimeZero ℓ)) ↔
      (ψ, χ) ∈ (shiftedWedgeExponential hm ℓ 1).graph := by
  rw [shiftedWedgeExponential, unitaryPartialTransport_mem_graph]
  have h := antilinearGraphSquare_unitary (oneParticleSpatialTranslation m (ℓ • e₁))
    (sourceTomitaGraph hm (leftWedgeTimeZero 0))
    (sourceTomitaGraph hm (leftWedgeTimeZero ℓ))
    (leftWedge_sourceTomitaGraph_translation hm ℓ)
    ((oneParticleSpatialTranslation m (ℓ • e₁)).symm ψ)
    ((oneParticleSpatialTranslation m (ℓ • e₁)).symm χ)
  simp only [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.trans (leftWedgeTomitaModularGraph_iff hm _ _)

theorem shiftedWedgePhysicalResolvent_fourier (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    shiftedWedgeFourier hm ℓ (sourcePhysicalResolvent hm (leftWedgeTimeZero ℓ) ψ) =
      exponentialResolvent rapidityMeasure (rapidityFrequencyExponent 1)
        (measurable_rapidityFrequencyExponent 1) (shiftedWedgeFourier hm ℓ ψ) := by
  have hg := (shiftedWedgeExponential_mem_graph hm ℓ 1 _ _).mp
    ((shiftedWedgeTomitaModularGraph_iff hm ℓ _ _).mp
      (sourcePhysicalResolvent_mem_square hm (leftWedgeTimeZero ℓ) ψ))
  rw [LinearPMap.mem_graph_iff] at hg
  obtain ⟨y, hy, hv⟩ := hg
  change (y : RapidityL2) = shiftedWedgeFourier hm ℓ
    (sourcePhysicalResolvent hm (leftWedgeTimeZero ℓ) ψ) at hy
  change rapidityExponential 1 y = shiftedWedgeFourier hm ℓ
    (ψ - sourcePhysicalResolvent hm (leftWedgeTimeZero ℓ) ψ) at hv
  symm
  have hr : exponentialResolvent rapidityMeasure (rapidityFrequencyExponent 1)
      (measurable_rapidityFrequencyExponent 1) (shiftedWedgeFourier hm ℓ ψ) = y := by
    apply (exponentialMultiplication_resolvent rapidityMeasure (rapidityFrequencyExponent 1)
      (measurable_rapidityFrequencyExponent 1) _ _).mp
    refine ⟨y.property, ?_⟩
    change (y : RapidityL2) + rapidityExponential 1 y = shiftedWedgeFourier hm ℓ ψ
    rw [hv, map_sub, hy]
    abel
  exact hr.trans hy

end VacuumBellSeparation
