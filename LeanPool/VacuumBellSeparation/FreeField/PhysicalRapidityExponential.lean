/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RapidityBoostFourier
public import LeanPool.VacuumBellSeparation.FreeField.ExponentialMultiplicationPositive
public import LeanPool.VacuumBellSeparation.FreeField.UnitaryPartialAdjoint

/-!
# The maximal positive rapidity exponentials in the physical Hilbert space

For the pinned Fourier convention and Δ^(it)=U(2πt), the candidate
real-power multiplier is exp(-4π²c ξ₁). We construct this precise maximal
operator, its full domain, positivity and half-square identity. Equality
with the actual wedge modular operator is a separate theorem, not a field
or assumption in this definition.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

/-- Rapidity frequency exponent given by `-4 * Real.pi ^ 2 * c * ⟪e₁, ξ⟫_ℝ`. -/
noncomputable def rapidityFrequencyExponent (c : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  -4 * Real.pi ^ 2 * c * ⟪e₁, ξ⟫_ℝ

theorem measurable_rapidityFrequencyExponent (c : ℝ) :
    Measurable (rapidityFrequencyExponent c) := by
  unfold rapidityFrequencyExponent
  fun_prop

/-- Linear map for the rapidity exponential, of type `RapidityL2 →ₗ.[ℂ] RapidityL2`. -/
noncomputable def rapidityExponential (c : ℝ) : RapidityL2 →ₗ.[ℂ] RapidityL2 :=
  exponentialMultiplication rapidityMeasure (rapidityFrequencyExponent c)
    (measurable_rapidityFrequencyExponent c)

theorem rapidityExponential_mem_graph (c : ℝ) (f g : RapidityL2) :
    (f, g) ∈ (rapidityExponential c).graph ↔
      g =ᵐ[rapidityMeasure] fun ξ => (Real.exp (rapidityFrequencyExponent c ξ) : ℂ) * f ξ :=
  exponentialMultiplication_mem_graph _ _ _ f g

theorem rapidityExponential_graph_half_square (c : ℝ) (f g : RapidityL2) :
    (f, g) ∈ (rapidityExponential c).graph ↔
      ∃ h : RapidityL2, (f, h) ∈ (rapidityExponential (c / 2)).graph ∧
        (h, g) ∈ (rapidityExponential (c / 2)).graph := by
  have he : (fun ξ => rapidityFrequencyExponent c ξ / 2) = rapidityFrequencyExponent (c / 2) := by
    funext ξ
    unfold rapidityFrequencyExponent
    ring
  simpa only [rapidityExponential, he] using
    exponentialMultiplication_graph_half_square rapidityMeasure
      (rapidityFrequencyExponent c) (measurable_rapidityFrequencyExponent c) f g

/-- The exact 4π² generator dictated by the real boost group; this is an
identity of actual scalar phase functions. -/
theorem rapidityBoostPhase_modular_parameter (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    rapidityBoostPhase (2 * Real.pi * t) ξ =
      Complex.exp (Complex.I * (t : ℂ) * (rapidityFrequencyExponent 1 ξ : ℂ)) := by
  unfold rapidityBoostPhase rapidityFrequencyExponent
  congr 1
  push_cast
  ring

/-- Linear map for the physical rapidity exponential, of type `Lp ℂ 2 (oneParticleMeasure m) →ₗ.[ℂ]
Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def physicalRapidityExponential {m : ℝ} (hm : 0 < m) (c : ℝ) :
    Lp ℂ 2 (oneParticleMeasure m) →ₗ.[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  unitaryPartialTransport (oneParticleRapidityFourier hm).symm (rapidityExponential c)

theorem physicalRapidityExponential_mem_graph_iff {m : ℝ} (hm : 0 < m) (c : ℝ)
    (f g : Lp ℂ 2 (oneParticleMeasure m)) :
    (f, g) ∈ (physicalRapidityExponential hm c).graph ↔
      (oneParticleRapidityFourier hm f, oneParticleRapidityFourier hm g) ∈
        (rapidityExponential c).graph :=
  unitaryPartialTransport_mem_graph (oneParticleRapidityFourier hm).symm _ f g

theorem physicalRapidityExponential_mem_graph {m : ℝ} (hm : 0 < m) (c : ℝ)
    (f g : Lp ℂ 2 (oneParticleMeasure m)) :
    (f, g) ∈ (physicalRapidityExponential hm c).graph ↔
      oneParticleRapidityFourier hm g =ᵐ[rapidityMeasure] fun ξ =>
        (Real.exp (rapidityFrequencyExponent c ξ) : ℂ) * oneParticleRapidityFourier hm f ξ := by
  rw [physicalRapidityExponential_mem_graph_iff, rapidityExponential_mem_graph]

theorem physicalRapidityExponential_mem_domain {m : ℝ} (hm : 0 < m) (c : ℝ)
    (f : Lp ℂ 2 (oneParticleMeasure m)) :
    f ∈ (physicalRapidityExponential hm c).domain ↔
      MemLp (fun ξ => (Real.exp (rapidityFrequencyExponent c ξ) : ℂ) *
        oneParticleRapidityFourier hm f ξ) 2 rapidityMeasure :=
  exponentialMultiplication_mem_domain _ _ _ _

theorem physicalRapidityExponential_isSelfAdjoint {m : ℝ} (hm : 0 < m) (c : ℝ) :
    IsSelfAdjoint (physicalRapidityExponential hm c) :=
  unitaryPartialTransport_isSelfAdjoint _ _ (exponentialMultiplication_isSelfAdjoint _ _ _)

theorem physicalRapidityExponential_inner_nonneg {m : ℝ} (hm : 0 < m) (c : ℝ)
    (f g : Lp ℂ 2 (oneParticleMeasure m))
    (hfg : (f, g) ∈ (physicalRapidityExponential hm c).graph) :
    0 ≤ (inner ℂ f g).re :=
  unitaryPartialTransport_inner_nonneg _ _ (exponentialMultiplication_inner_nonneg _ _ _) f g hfg

theorem physicalRapidityExponential_graph_half_square {m : ℝ} (hm : 0 < m) (c : ℝ)
    (f g : Lp ℂ 2 (oneParticleMeasure m)) :
    (f, g) ∈ (physicalRapidityExponential hm c).graph ↔
      ∃ h : Lp ℂ 2 (oneParticleMeasure m),
        (f, h) ∈ (physicalRapidityExponential hm (c / 2)).graph ∧
        (h, g) ∈ (physicalRapidityExponential hm (c / 2)).graph := by
  constructor
  · intro hfg
    obtain ⟨h, hfh, hhg⟩ := (rapidityExponential_graph_half_square c _ _).mp
      ((physicalRapidityExponential_mem_graph_iff hm c f g).mp hfg)
    refine ⟨(oneParticleRapidityFourier hm).symm h, ?_, ?_⟩
    · rw [physicalRapidityExponential_mem_graph_iff, LinearIsometryEquiv.apply_symm_apply]
      exact hfh
    · rw [physicalRapidityExponential_mem_graph_iff, LinearIsometryEquiv.apply_symm_apply]
      exact hhg
  · rintro ⟨h, hfh, hhg⟩
    apply (physicalRapidityExponential_mem_graph_iff hm c f g).mpr
    apply (rapidityExponential_graph_half_square c _ _).mpr
    exact ⟨oneParticleRapidityFourier hm h,
      (physicalRapidityExponential_mem_graph_iff hm (c / 2) f h).mp hfh,
      (physicalRapidityExponential_mem_graph_iff hm (c / 2) h g).mp hhg⟩

end VacuumBellSeparation
