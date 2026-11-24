/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionRegularizationFinal

/-!
# A zero-Levi distribution has a genuine smooth local representative

One internally selected adapted radial family is applied to both `S` and `-S`.
Its actual two antitonicity inequalities force all regularized values to equal
the zeroth one on the inner domain.  The genuine transpose approximate identity
then identifies the full restricted distribution with that smooth density.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.ActualZeroLeviDistributionSmoothness

open AdaptedRadialKernel FirstPass

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual vanishing of every directional Levi distribution produces a smooth
representative, local integrability and the complete restricted distribution
identity, on an internally chosen neighborhood. -/
theorem exists_smooth_local_representative_of_zero_levi
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E} (S : 𝓓'(Ω, ℝ))
    (hzero : ∀ v : E, distributionalLeviCLM v S = 0)
    (x : E) (hx : x ∈ Ω) :
    ∃ (U : Opens E) (hU : U ≤ Ω) (f : E → ℝ),
      x ∈ U ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∃ hf : LocallyIntegrableOn f U μ,
        restrictDistribution S hU = regularDistribution μ f hf ∧
        ∀ z ∈ U, ∀ v : E, leviForm f z v = 0 := by
  let D : AdaptedRadialKernelData μ Ω x :=
    Classical.choice (exists_adaptedRadialKernelData μ hx)
  have hpos : HasNonnegativeDistributionalLevi S := by
    intro v φ _hφ
    rw [hzero v]
    exact le_refl 0
  have hneg : HasNonnegativeDistributionalLevi (-S) := by
    intro v φ _hφ
    rw [map_neg, hzero v]
    simp only [neg_zero, zero_apply, le_refl]
  have heq : ∀ j : ℕ, ∀ z ∈ D.inner,
      D.distributionRegularizedValue S j z =
        D.distributionRegularizedValue S 0 z := by
    intro j z hz
    have hle := D.distributionRegularizedValue_antitone S hpos
      (Nat.zero_le j) (subset_closure hz)
    have hge := D.distributionRegularizedValue_antitone (-S) hneg
      (Nat.zero_le j) (subset_closure hz)
    change -D.distributionRegularizedValue S j z ≤
      -D.distributionRegularizedValue S 0 z at hge
    exact le_antisymm hle (neg_le_neg_iff.mp hge)
  have hsm := D.distributionRegularizedValue_contDiff S 0
  have hf : LocallyIntegrableOn (D.distributionRegularizedValue S 0) D.inner μ :=
    hsm.continuous.locallyIntegrable.locallyIntegrableOn _
  refine ⟨D.inner, D.inner_le, D.distributionRegularizedValue S 0,
    D.center_mem, hsm, hf, ?_, ?_⟩
  · ext φ
    have ht : Tendsto
        (fun j ↦ ∫ z, φ z * D.distributionRegularizedValue S j z ∂μ)
        atTop (𝓝 ((restrictDistribution S D.inner_le) φ)) := by
      have hpairing := Filter.Tendsto.comp S.continuous.continuousAt
        (D.tendsto_ambientConvolutionTestFunction φ)
      rw [restrictDistribution_apply]
      refine hpairing.congr fun j ↦ ?_
      exact (D.distribution_convolution_transpose S j φ).symm
    have hconstant : (fun j ↦ ∫ z, φ z * D.distributionRegularizedValue S j z ∂μ) =
        (fun _j : ℕ ↦ ∫ z, φ z * D.distributionRegularizedValue S 0 z ∂μ) := by
      funext j
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ D.inner
      · rw [heq j z hz]
      · have hz0 : φ z = 0 := by
          by_contra hnon
          exact hz (φ.tsupport_subset (subset_tsupport φ hnon))
        rw [hz0]
        simp only [zero_mul]
    rw [regularDistribution_apply]
    rw [hconstant] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  · intro z hz v
    rw [D.leviForm_distributionRegularizedValue_eq S 0 (subset_closure hz) v,
      hzero v]
    rfl

end SGPT.Foundations.Analysis.Pending.ActualZeroLeviDistributionSmoothness
