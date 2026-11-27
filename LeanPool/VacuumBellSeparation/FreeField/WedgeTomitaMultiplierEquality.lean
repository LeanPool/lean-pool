/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeTomitaMultiplierInclusion
public import LeanPool.VacuumBellSeparation.FreeField.WedgeReflectionBoost
public import LeanPool.VacuumBellSeparation.FreeField.GaussianRapidityRegularization
public import LeanPool.VacuumBellSeparation.FreeField.InjectiveSourceTomita

/-!
# Full original wedge Tomita graph equals the maximal reflected half-power

Gaussian regularization has two proved properties: it preserves the original
closed source graph, and its maximal half-power is bounded on the entire Hilbert
space. Density extends each regularized graph to every input; strong Gaussian
convergence then gives the reverse inclusion with the entire maximal domain.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology Gaussian.HilbertComplexification

variable {m : ℝ} (hm : 0 < m)

theorem wedgeRapidityTomitaGraph_snd_unique {ψ χ χ' : Lp ℂ 2 (oneParticleMeasure m)}
    (h : (ψ, χ) ∈ wedgeRapidityTomitaGraph hm)
    (h' : (ψ, χ') ∈ wedgeRapidityTomitaGraph hm) : χ = χ' := by
  have he := (physicalRapidityExponential hm (1 / 2)).mem_graph_snd_inj h h' rfl
  have hj := congrArg (physicalWedgeReflection hm) he
  simpa only [physicalWedgeReflection_involutive] using hj

/-- Continuous linear map for the physical Gaussian Tomita, of type `Lp ℂ 2 (oneParticleMeasure m)
→L[ℝ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def physicalGaussianTomita {ε : ℝ} (hε : ε ≠ 0) :
    Lp ℂ 2 (oneParticleMeasure m) →L[ℝ] Lp ℂ 2 (oneParticleMeasure m) :=
  (physicalWedgeReflection hm).comp ((physicalGaussianHalf hm hε).restrictScalars ℝ)

theorem gaussian_regularized_mem_wedgeRapidityTomitaGraph {ε : ℝ} (hε : ε ≠ 0)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    (gaussianBoostAverage hm ε ψ, physicalGaussianTomita hm hε ψ) ∈
      wedgeRapidityTomitaGraph hm := by
  change (gaussianBoostAverage hm ε ψ,
    physicalWedgeReflection hm (physicalWedgeReflection hm (physicalGaussianHalf hm hε ψ))) ∈
      (physicalRapidityExponential hm (1 / 2)).graph
  rw [physicalWedgeReflection_involutive]
  exact gaussianBoostAverage_mem_physicalHalf_graph hm hε ψ

/-- Every regularized vector is in the actual original source domain. The
bounded second coordinate and source-domain density discharge the extension. -/
theorem gaussian_regularized_mem_sourceTomitaGraph {ε : ℝ} (hε : ε ≠ 0)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    (gaussianBoostAverage hm ε ψ, physicalGaussianTomita hm hε ψ) ∈
      sourceTomitaGraph hm (leftWedgeTimeZero 0) := by
  have hd := complexSourceMap_denseRange_of_open hm (leftWedgeTimeZero 0)
    (isOpen_leftWedgeTimeZero 0) (leftWedgeTimeZero_nonempty 0)
  refine hd.induction_on (p := fun ψ =>
    (gaussianBoostAverage hm ε ψ, physicalGaussianTomita hm hε ψ) ∈
      sourceTomitaGraph hm (leftWedgeTimeZero 0)) ψ ?_ ?_
  · exact (sourceTomitaGraph_isClosed hm (leftWedgeTimeZero 0)).preimage
      ((gaussianBoostAverage hm ε).continuous.prodMk (physicalGaussianTomita hm hε).continuous)
  · intro z
    have hΓ : (complexSourceMap hm (leftWedgeTimeZero 0) z,
        complexSourceMap hm (leftWedgeTimeZero 0) (conjugation z)) ∈
          sourceTomitaGraph hm (leftWedgeTimeZero 0) := ⟨z, rfl, rfl⟩
    have hA := gaussianBoostAverage_preserves_sourceTomitaGraph hm ε hΓ
    have he := wedgeRapidityTomitaGraph_snd_unique hm
      (sourceTomitaGraph_subset_wedgeRapidityTomitaGraph hm hA)
      (gaussian_regularized_mem_wedgeRapidityTomitaGraph hm hε
        (complexSourceMap hm (leftWedgeTimeZero 0) z))
    rwa [he] at hA

theorem gaussianBoostAverage_preserves_wedgeRapidityTomitaGraph (ε : ℝ)
    {ψ χ : Lp ℂ 2 (oneParticleMeasure m)}
    (hψχ : (ψ, χ) ∈ wedgeRapidityTomitaGraph hm) :
    (gaussianBoostAverage hm ε ψ, gaussianBoostAverage hm ε χ) ∈
      wedgeRapidityTomitaGraph hm := by
  change (gaussianBoostAverage hm ε ψ,
    physicalWedgeReflection hm (gaussianBoostAverage hm ε χ)) ∈
      (physicalRapidityExponential hm (1 / 2)).graph
  rw [physicalWedgeReflection_gaussianBoostAverage]
  exact gaussianBoostAverage_preserves_physicalHalf_graph hm ε hψχ

theorem wedgeRapidityTomitaGraph_subset_sourceTomitaGraph :
    wedgeRapidityTomitaGraph hm ⊆ sourceTomitaGraph hm (leftWedgeTimeZero 0) := by
  rintro ⟨ψ, χ⟩ hψχ
  have hA (ε : ℝ) (hε : ε ≠ 0) :
      (gaussianBoostAverage hm ε ψ, gaussianBoostAverage hm ε χ) ∈
        sourceTomitaGraph hm (leftWedgeTimeZero 0) := by
    have hΓ := gaussian_regularized_mem_sourceTomitaGraph hm hε ψ
    have he := wedgeRapidityTomitaGraph_snd_unique hm
      (gaussian_regularized_mem_wedgeRapidityTomitaGraph hm hε ψ)
      (gaussianBoostAverage_preserves_wedgeRapidityTomitaGraph hm ε hψχ)
    rwa [he] at hΓ
  have ht : Tendsto (fun ε : ℝ =>
      (gaussianBoostAverage hm ε ψ, gaussianBoostAverage hm ε χ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (ψ, χ)) :=
    ((tendsto_gaussianBoostAverage hm ψ).mono_left nhdsWithin_le_nhds).prodMk_nhds
      ((tendsto_gaussianBoostAverage hm χ).mono_left nhdsWithin_le_nhds)
  apply (sourceTomitaGraph_isClosed hm (leftWedgeTimeZero 0)).mem_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hA ε hε

/-- Equality retains the maximal multiplier domain and the full original
halfspace source graph, with no BW, strip-domain or core-density assumption. -/
theorem sourceTomitaGraph_eq_wedgeRapidityTomitaGraph :
    sourceTomitaGraph hm (leftWedgeTimeZero 0) = wedgeRapidityTomitaGraph hm :=
  Set.Subset.antisymm (sourceTomitaGraph_subset_wedgeRapidityTomitaGraph hm)
    (wedgeRapidityTomitaGraph_subset_sourceTomitaGraph hm)

theorem leftWedgeSourceTomita_full_graph (ψ χ : Lp ℂ 2 (oneParticleMeasure m)) :
    (∃ hψ : ψ ∈ (leftWedgeSourceTomita hm 0).domain,
      leftWedgeSourceTomita hm 0 ⟨ψ, hψ⟩ = χ) ↔
      (ψ, physicalWedgeReflection hm χ) ∈ (physicalRapidityExponential hm (1 / 2)).graph := by
  calc
    _ ↔ (ψ, χ) ∈ sourceTomitaGraph hm (leftWedgeTimeZero 0) :=
      (injectiveSourceTomita_graph hm (leftWedgeTimeZero 0)
        (complexSourceMap_injective_leftWedgeTimeZero hm 0) ψ χ).symm
    _ ↔ _ := by
      rw [sourceTomitaGraph_eq_wedgeRapidityTomitaGraph]
      rfl

end VacuumBellSeparation
