/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionTranslationJets

/-!
# Differentiating fixed-support distribution pairings

This file separates the functional-analytic pairing step from the later Taylor
estimate for translated kernels.  A little-o remainder in one controlling
seminorm remains little-o after applying a linearly seminorm-bounded scalar
functional.  The distribution-specialized form obtains such a seminorm bound
from the finite-order estimate for distributions on one compact support.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Filter Asymptotics
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending

/-- The first translation jet of a cutoff-translated kernel, bundled as a
linear map in its direction.  Continuity into the fixed-support Frechet space
is deliberately not asserted or needed here. -/
noncomputable def cutoffTranslatedKernelFirstJetLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z : E) :
    E →ₗ[ℝ] ContDiffMapSupportedIn E ℝ ⊤ K where
  toFun v :=
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK 1 z (fun _ => v)
  map_add' v w := by
    ext y
    simp [cutoffTranslatedKernelJetSupportedIn_apply, map_add, mul_add]
    ring
  map_smul' c v := by
    ext y
    simp [cutoffTranslatedKernelJetSupportedIn_apply, map_smul]
    ring

@[simp]
theorem cutoffTranslatedKernelFirstJetLM_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z v : E) :
    cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z v =
      cutoffTranslatedKernelJetSupportedIn
        χ κ hκ K hχK 1 z (fun _ => v) :=
  rfl

/-- A scalar linear functional bounded by one seminorm preserves the
first-order Frechet remainder.  Finite dimensionality supplies continuity of
the composite candidate derivative. -/
theorem hasFDerivAt_linear_of_seminorm_remainder
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup A] [Module ℝ A]
    (p : Seminorm ℝ A) (L : A →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ a : A, |L a| ≤ C * p a)
    (Φ : E → A) (Ψ : E →ₗ[ℝ] A) (z : E)
    (hrem : (fun h : E => p (Φ (z + h) - Φ z - Ψ h)) =o[𝓝 0]
      (fun h : E => h)) :
    HasFDerivAt (fun w => L (Φ w))
      ⟨L.comp Ψ, (L.comp Ψ).continuous_of_finiteDimensional⟩ z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hb :
      (fun h : E => L (Φ (z + h)) - L (Φ z) - (L.comp Ψ) h) =O[𝓝 0]
        (fun h : E => C * p (Φ (z + h) - Φ z - Ψ h)) := by
    apply (IsBigOWith.of_bound (c := (1 : ℝ)) ?_).isBigO
    filter_upwards with h
    simpa [map_sub, Real.norm_eq_abs, abs_of_nonneg hC,
      abs_of_nonneg (apply_nonneg p _)]
      using hL (Φ (z + h) - Φ z - Ψ h)
  exact hb.trans_isLittleO (hrem.const_mul_left C)

/-- A finite-order sup-seminorm Taylor remainder for the fixed-support
translated kernels implies differentiability of their pairing with a
distribution.  The required seminorm order and bound are supplied by the
distribution's continuity on the fixed compact support. -/
theorem distributionPairing_hasFDerivAt_of_supSeminorm_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z : E)
    (hrem : ∀ m : ℕ,
      (fun h : E =>
        ((Finset.Iic m).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K))
          (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK (z + h) -
            cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z -
            cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z h))
        =o[𝓝 0] (fun h : E => h)) :
    HasFDerivAt
      (fun w => distributionOnSupportedInCLM T K hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK w))
      ⟨(distributionOnSupportedInCLM T K hKΩ).toLinearMap.comp
          (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z),
        ((distributionOnSupportedInCLM T K hKΩ).toLinearMap.comp
          (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z)).continuous_of_finiteDimensional⟩
      z := by
  obtain ⟨m, C, _hC, hbound⟩ :=
    exists_finite_order_seminorm_bound_on_compact T K hKΩ
  apply hasFDerivAt_linear_of_seminorm_remainder
    ((Finset.Iic m).sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K))
    (distributionOnSupportedInCLM T K hKΩ).toLinearMap (C : ℝ) C.coe_nonneg
  · intro φ
    simpa [distributionOnSupportedInCLM_apply] using hbound φ
  · exact hrem m

end SGPT.Foundations.Analysis.Pending
