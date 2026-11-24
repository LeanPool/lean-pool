/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DeficitConvolution
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DeficitLocalization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.TestLeviPairing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.CompactDiscLocalization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularDistribution

/-!
# Distributional Levi positivity for singular disc-PSH potentials

For a potential satisfying the actual complex-disc submean criterion, compact
localization of its finite-majorant deficit yields a nonnegative integrable
density. The weighted supermean theorem and the test-function cancellation
identity then give positivity of every distributional Levi derivative.

On a nontrivial preconnected open domain the required local integrability and
almost-everywhere finiteness are supplied by the proved PSH integrability
theorem. No global disc criterion is inferred from arbitrary ambient PSH germs.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]
variable {Ω : Opens E} {u : E → EReal}

/-- A singular disc-PSH potential which is locally integrable and finite almost
everywhere has nonnegative distributional Levi derivatives. The integral
positivity is proved for every actual nonnegative compactly supported test
function, rather than assumed as part of the PSH definition. -/
theorem DiscPshOn.hasNonnegativeDistributionalLevi_of_locallyIntegrable
    (hu : DiscPshOn u Ω)
    (huL : LocallyIntegrableOn (fun x => (u x).toReal) Ω μ)
    (hfin : ∀ᵐ x ∂μ.restrict Ω, u x ≠ ⊤ ∧ u x ≠ ⊥) :
    HasNonnegativeDistributionalLevi
      (regularDistribution μ (fun x => (u x).toReal) huL) := by
  intro v φ hφn
  obtain ⟨R, hR, K, hK, hKΩ, hφK, hdiscs⟩ :=
    exists_compact_affineClosedDisc_family φ.hasCompactSupport Ω.isOpen φ.tsupport_subset v
  have hmajorant : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, u x ≤ (C : EReal) := by
    by_cases hne : K.Nonempty
    · obtain ⟨C, hC⟩ := hu.exists_compact_upper_bound hK hne hKΩ
      refine ⟨Max.max C 0, le_max_right C 0, ?_⟩
      intro x hx
      exact (hC x hx).trans (EReal.coe_le_coe_iff.mpr (le_max_left C 0))
    · refine ⟨0, le_rfl, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  obtain ⟨C, hC0, hC⟩ := hmajorant
  let f : E → ℝ := K.indicator (fun x => C - (u x).toReal)
  have hf : LocallyIntegrable f μ :=
    locallyIntegrable_indicator_realDeficit_of_isCompact hK hKΩ huL C
  have hfn : ∀ x, 0 ≤ f x := indicator_realDeficit_nonneg hC0 hC
  have hD : K.indicator (fun x => ((C : EReal) - u x).toENNReal) =ᵐ[μ]
      fun x => ENNReal.ofReal (f x) :=
    indicator_deficit_ae_eq_ofReal_of_isCompact hK hKΩ hfin C
  have hφ2 : ContDiff ℝ 2 (φ : E → ℝ) :=
    φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hpair := hu.integral_deficit_mul_leviForm_nonpos hK.measurableSet hKΩ C hC
    hD hf hfn φ.hasCompactSupport hφ2 hφn v hR (by
      intro r hr x hx
      exact hdiscs x (subset_closure hx) r hr.2.le)
  change (∫ x, K.indicator (fun y => C - (u y).toReal) x * leviForm φ x v ∂μ) ≤ 0 at hpair
  rw [integral_indicator_deficit_mul_leviForm_testFunction huL φ hφK C v] at hpair
  exact neg_nonpos.mp hpair

/-- A nontrivial disc-PSH potential on a preconnected open domain induces an
actual regular distribution with nonnegative Levi derivatives. Local
integrability and a.e. finiteness are consequences of the stated hypotheses. -/
theorem DiscPshOn.pshRegularDistribution_hasNonnegativeDistributionalLevi
    (hu : DiscPshOn u Ω) (hΩ : IsPreconnected (Ω : Set E))
    (hne : ∃ a ∈ Ω, u a ≠ ⊥) :
    HasNonnegativeDistributionalLevi
      (pshRegularDistribution (hu.plurisubharmonicOn Ω.isOpen) μ hΩ hne) := by
  apply hu.hasNonnegativeDistributionalLevi_of_locallyIntegrable
  exact (hu.plurisubharmonicOn Ω.isOpen).ae_finite μ hΩ hne

end SGPT.Foundations.Analysis
