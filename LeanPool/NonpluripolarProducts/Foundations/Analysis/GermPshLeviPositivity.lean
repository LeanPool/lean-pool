/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LocalPshDiscControl
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DeficitConvolution
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DeficitLocalization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.TestLeviPairing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.CompactDiscLocalization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularDistribution
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.WeightedPairingSupermean

/-!
# Distributional Levi positivity from local PSH germs

The compact support of a test function has a uniform small-disc radius, even
though different centers may use different PSH neighborhoods. Intersecting
this radius bound with the compact-localization radius keeps one deficit
density fixed throughout the angular averaging argument.

The resulting inequalities prove distributional Levi positivity directly from
local PSH germs. No global complex-disc criterion on the entire domain is
assumed or inferred.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff ENNReal

namespace SGPT.Foundations.Analysis

section AngularBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {u : E → EReal} {U S K : Set E}

/-- A compact family of PSH germs gives one angular inequality for a fixed
localized deficit at every sufficiently small radius. The compact set used
for localization need not itself satisfy a global disc criterion. -/
theorem PlurisubharmonicOn.exists_uniform_indicator_deficit_bound
    (hu : PlurisubharmonicOn u U) (hS : IsCompact S) (hSU : S ⊆ U)
    (v : E) {R₀ : ℝ} (hR₀ : 0 < R₀) (hSK : S ⊆ K)
    (hdiscs : ∀ x ∈ S, ∀ r : ℝ, r ≤ R₀ → affineClosedDisc x v r ⊆ K)
    (C : ℝ) (hC : ∀ y ∈ K, u y ≤ (C : EReal)) :
    ∃ R > 0, ∀ r ∈ Ioo 0 R, ∀ x ∈ S,
      (∫⁻ t in Ioc 0 (2 * Real.pi),
        K.indicator (fun y => ((C : EReal) - u y).toENNReal)
          (x + circleMap 0 r t • v)) ≤
        ENNReal.ofReal (2 * Real.pi) *
          K.indicator (fun y => ((C : EReal) - u y).toENNReal) x := by
  classical
  obtain ⟨Rg, hRg, hbound⟩ := hu.exists_uniform_circleDeficit_bound hS hSU v
  refine ⟨Min.min Rg R₀, lt_min hRg hR₀, ?_⟩
  intro r hr x hx
  have hrg : r ≤ Rg := hr.2.le.trans (min_le_left _ _)
  have hr₀ : r ≤ R₀ := hr.2.le.trans (min_le_right _ _)
  have hdisc := hdiscs x hx r hr₀
  have hpoint := hbound x hx r hr.1 hrg C (fun y hy => hC y (hdisc hy))
  have hcircle (t : ℝ) :
      K.indicator (fun y => ((C : EReal) - u y).toENNReal)
        (x + circleMap 0 r t • v) =
          ((C : EReal) - u (x + circleMap 0 r t • v)).toENNReal :=
    Set.indicator_of_mem (hdisc (circle_mem_affineClosedDisc x v hr.1.le t)) _
  have hcenter : K.indicator (fun y => ((C : EReal) - u y).toENNReal) x =
      ((C : EReal) - u x).toENNReal := Set.indicator_of_mem (hSK hx) _
  simpa only [circleDeficit, hcircle, hcenter] using hpoint

end AngularBound

section Positivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]
variable {Ω : Opens E} {u : E → EReal}

/-- Actual local PSH germs, together with local integrability and a.e.
finiteness, produce a regular distribution with nonnegative Levi derivatives.
Uniformity is required only near the compact support of each individual test
function, and follows from the original germs. -/
theorem PlurisubharmonicOn.hasNonnegativeDistributionalLevi_of_locallyIntegrable
    (hu : PlurisubharmonicOn u Ω)
    (huL : LocallyIntegrableOn (fun x => (u x).toReal) Ω μ)
    (hfin : ∀ᵐ x ∂μ.restrict Ω, u x ≠ ⊤ ∧ u x ≠ ⊥) :
    HasNonnegativeDistributionalLevi
      (regularDistribution μ (fun x => (u x).toReal) huL) := by
  intro v φ hφn
  obtain ⟨Rc, hRc, K, hK, hKΩ, hφK, hdiscs⟩ :=
    exists_compact_affineClosedDisc_family φ.hasCompactSupport Ω.isOpen φ.tsupport_subset v
  obtain ⟨C, hC0, hC⟩ := hu.exists_nonnegative_compact_upper_bound hK hKΩ
  obtain ⟨R, hR, hangular⟩ := hu.exists_uniform_indicator_deficit_bound
    φ.hasCompactSupport φ.tsupport_subset v hRc hφK hdiscs C hC
  let f : E → ℝ := K.indicator (fun x => C - (u x).toReal)
  let D : E → ℝ≥0∞ := K.indicator (fun x => ((C : EReal) - u x).toENNReal)
  have hf : LocallyIntegrable f μ :=
    locallyIntegrable_indicator_realDeficit_of_isCompact hK hKΩ huL C
  have hfn : ∀ x, 0 ≤ f x := indicator_realDeficit_nonneg hC0 hC
  have hDm : Measurable D := hu.measurable_indicator_deficit hK.measurableSet hKΩ C
  have hDf : D =ᵐ[μ] fun x => ENNReal.ofReal (f x) :=
    indicator_deficit_ae_eq_ofReal_of_isCompact hK hKΩ hfin C
  have hφ2 : ContDiff ℝ 2 (φ : E → ℝ) :=
    φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hpair := integral_mul_leviForm_nonpos_of_pointwise_circle_lintegral
    hDm hDf hf hfn φ.hasCompactSupport hφ2 hφn v hR (by
      intro r hr x hx
      exact hangular r hr x (subset_closure hx))
  change (∫ x, K.indicator (fun y => C - (u y).toReal) x * leviForm φ x v ∂μ) ≤ 0 at hpair
  rw [integral_indicator_deficit_mul_leviForm_testFunction huL φ hφK C v] at hpair
  exact neg_nonpos.mp hpair

/-- A nontrivial PSH potential on a preconnected open domain defines an actual
regular distribution with nonnegative distributional Levi form. Both local
integrability and almost-everywhere finiteness follow from PSH, and no
global-disc hypothesis is present. -/
theorem PlurisubharmonicOn.pshRegularDistribution_hasNonnegativeDistributionalLevi
    (hu : PlurisubharmonicOn u Ω) (hΩ : IsPreconnected (Ω : Set E))
    (hne : ∃ a ∈ Ω, u a ≠ ⊥) :
    HasNonnegativeDistributionalLevi (pshRegularDistribution hu μ hΩ hne) := by
  apply hu.hasNonnegativeDistributionalLevi_of_locallyIntegrable
  exact hu.ae_finite μ hΩ hne

/-- A locally integrable disc-PSH potential with a.e. finite values induces
a regular distribution with nonnegative Levi derivatives. -/
theorem DiscPshOn.hasNonnegativeDistributionalLevi_of_locallyIntegrable
    (hu : DiscPshOn u Ω)
    (huL : LocallyIntegrableOn (fun x => (u x).toReal) Ω μ)
    (hfin : ∀ᵐ x ∂μ.restrict Ω, u x ≠ ⊤ ∧ u x ≠ ⊥) :
    HasNonnegativeDistributionalLevi
      (regularDistribution μ (fun x => (u x).toReal) huL) :=
  (hu.plurisubharmonicOn Ω.isOpen).hasNonnegativeDistributionalLevi_of_locallyIntegrable huL hfin

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

end Positivity

end SGPT.Foundations.Analysis
