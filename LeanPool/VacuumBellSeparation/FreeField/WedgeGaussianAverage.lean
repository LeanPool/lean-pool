/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeSpacetimeTomitaCore
public import LeanPool.VacuumBellSeparation.FreeField.OneParticleBoostContinuity
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Convex.Integral

/-!
# Genuine Gaussian averages preserving the entire original wedge graph

A fixed standard real Gaussian probability measure averages U(εt). The Bochner
integral is a bounded complex-linear contraction. Its graph action preserves
the closed real-convex source Tomita graph, and it converges strongly to the
identity as ε tends to zero. No spectral-domain assertion is assumed here.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ProbabilityTheory Filter Topology ClosedSubmodule
  Gaussian.HilbertComplexification
open scoped ComplexConjugate

variable {m : ℝ} (hm : 0 < m)

theorem integrable_gaussian_boost (ε : ℝ) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    Integrable (fun t : ℝ => oneParticleBoost hm (ε * t) ψ) (gaussianReal 0 1) := by
  apply (integrable_const ‖ψ‖).mono'
    ((continuous_oneParticleBoost hm ψ).comp (continuous_const.mul
      continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall fun t => (oneParticleBoost hm (ε * t)).norm_map ψ |>.le

/-- Continuous linear map for the gaussian boost average, of type `Lp ℂ 2 (oneParticleMeasure m)
→L[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def gaussianBoostAverage (ε : ℝ) :
    Lp ℂ 2 (oneParticleMeasure m) →L[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ∫ t : ℝ, oneParticleBoost hm (ε * t) ψ ∂gaussianReal 0 1
      map_add' := by
        intro ψ χ
        simp only [map_add]
        exact integral_add (integrable_gaussian_boost hm ε ψ) (integrable_gaussian_boost hm ε χ)
      map_smul' := by
        intro c ψ
        simp only [map_smul, integral_smul, RingHom.id_apply] }
    1 (fun ψ => by
      simpa using (norm_integral_le_of_norm_le_const
        (μ := gaussianReal 0 1) (f := fun t : ℝ => oneParticleBoost hm (ε * t) ψ)
        (C := ‖ψ‖) (Eventually.of_forall fun t => (oneParticleBoost hm (ε * t)).norm_map ψ |>.le)))

theorem gaussianBoostAverage_apply (ε : ℝ) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    gaussianBoostAverage hm ε ψ = ∫ t : ℝ, oneParticleBoost hm (ε * t) ψ ∂gaussianReal 0 1 := rfl

theorem tendsto_gaussianBoostAverage (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    Tendsto (fun ε : ℝ => gaussianBoostAverage hm ε ψ) (𝓝 0) (𝓝 ψ) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := gaussianReal 0 1) (F := fun ε t : ℝ => oneParticleBoost hm (ε * t) ψ)
    (f := fun _ => ψ) (fun _ => ‖ψ‖)
    (Eventually.of_forall fun ε => (integrable_gaussian_boost hm ε ψ).aestronglyMeasurable)
    (Eventually.of_forall fun ε => Eventually.of_forall fun t =>
      (oneParticleBoost hm (ε * t)).norm_map ψ |>.le)
    (integrable_const _) (Eventually.of_forall fun t => by
      have ht := (continuous_oneParticleBoost hm ψ).continuousAt.tendsto.comp
        (show Tendsto (fun ε : ℝ => ε * t) (𝓝 0) (𝓝 0) by
          simpa using (tendsto_id.mul_const t : Tendsto (fun ε : ℝ => ε * t) (𝓝 0) (𝓝 (0 * t))))
      simpa only [Function.comp_def, show oneParticleBoost hm 0 ψ = ψ from
        oneParticleBoostIsometry_zero hm ψ] using ht)
  simpa only [gaussianBoostAverage_apply, integral_const, probReal_univ, one_smul] using h

theorem sourceTomitaGraph_convex (U : Set (EuclideanSpace ℝ (Fin 3))) :
    Convex ℝ (sourceTomitaGraph hm U) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨z, hz₁, hz₂⟩ := hp
  obtain ⟨w, hw₁, hw₂⟩ := hq
  refine ⟨(a : ℂ) • z + (b : ℂ) • w, ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, hz₁, hw₁]
    change (a : ℂ) • p.1 + (b : ℂ) • q.1 = a • p.1 + b • q.1
    rfl
  · rw [map_add]
    rw [conjugation.map_smulₛₗ, conjugation.map_smulₛₗ]
    rw [show starRingEnd ℂ (a : ℂ) = (a : ℂ) from Complex.conj_ofReal a,
      show starRingEnd ℂ (b : ℂ) = (b : ℂ) from Complex.conj_ofReal b]
    rw [map_add, map_smul, map_smul, hz₂, hw₂]
    change (a : ℂ) • p.2 + (b : ℂ) • q.2 = a • p.2 + b • q.2
    rfl

theorem sourceTomitaGraph_boost_invariant (η : ℝ)
    {p : Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)}
    (hp : p ∈ sourceTomitaGraph hm (leftWedgeTimeZero 0)) :
    (oneParticleBoost hm η p.1, oneParticleBoost hm η p.2) ∈
      sourceTomitaGraph hm (leftWedgeTimeZero 0) := by
  have hc : IsClosed {q : Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m) |
      (oneParticleBoost hm η q.1, oneParticleBoost hm η q.2) ∈
        sourceTomitaGraph hm (leftWedgeTimeZero 0)} :=
    (sourceTomitaGraph_isClosed hm (leftWedgeTimeZero 0)).preimage
      (((oneParticleBoost hm η).continuous.comp continuous_fst).prodMk
        ((oneParticleBoost hm η).continuous.comp continuous_snd))
  have hs : wedgeSpacetimeTomitaTestGraph hm 0 ⊆
      {q | (oneParticleBoost hm η q.1, oneParticleBoost hm η q.2) ∈
        sourceTomitaGraph hm (leftWedgeTimeZero 0)} := by
    intro q hq
    exact wedgeSpacetimeTomitaTestGraph_subset hm 0
      (wedgeSpacetimeTomitaTestGraph_boost_invariant hm η hq)
  have h := closure_minimal hs hc
  rw [closure_wedgeSpacetimeTomitaTestGraph] at h
  exact h hp

theorem gaussianBoostAverage_preserves_sourceTomitaGraph (ε : ℝ)
    {ψ χ : Lp ℂ 2 (oneParticleMeasure m)}
    (hψχ : (ψ, χ) ∈ sourceTomitaGraph hm (leftWedgeTimeZero 0)) :
    (gaussianBoostAverage hm ε ψ, gaussianBoostAverage hm ε χ) ∈
      sourceTomitaGraph hm (leftWedgeTimeZero 0) := by
  have h := (sourceTomitaGraph_convex hm (leftWedgeTimeZero 0)).integral_mem
    (μ := gaussianReal 0 1) (sourceTomitaGraph_isClosed hm (leftWedgeTimeZero 0))
    (Eventually.of_forall fun t => sourceTomitaGraph_boost_invariant hm (ε * t) hψχ)
    ((integrable_gaussian_boost hm ε ψ).prodMk (integrable_gaussian_boost hm ε χ))
  simpa only [integral_pair (integrable_gaussian_boost hm ε ψ)
    (integrable_gaussian_boost hm ε χ), gaussianBoostAverage_apply] using h

end VacuumBellSeparation
