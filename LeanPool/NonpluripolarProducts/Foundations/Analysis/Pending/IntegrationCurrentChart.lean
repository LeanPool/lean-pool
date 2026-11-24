/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ClosedTopCurrents

/-!
# The integration current read in one chart

Source: the change of variables for the Kähler volume in a chart (`ClosedTopCurrents.
setIntegral_kahlerVolume_image`).  TN.4 plan, step B6, finding F6 route (i)
: both the positivity-to-Levi link and the identity
`R_ε = m_ε b + ddᶜ v_ε` evaluate currents on test forms supported in one chart,
    where the pairing is
an integral of the top density of the form in that chart.

* `integrationCurrent_apply_eq_setIntegral`: if `φ / ωⁿ` vanishes off `e⁻¹(K)` (`K` measurable in
    the
  chart target), then `[X] φ = ∫_K topDensity(φ_e) dλ`.
* `integrationCurrent_apply_eq_integral`: the same with the integral over the whole model space
    when
  the coefficient also vanishes off `K`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.IntegrationCurrentChart

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent TopDegreeDensity ClosedTopCurrents

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The integration current in one chart**: `[X] φ = ∫_K topDensity(φ_e) dλ` when `φ / ωⁿ`
vanishes off `e⁻¹(K)`. -/
theorem integrationCurrent_apply_eq_setIntegral (w : KahlerBackground (m + 1) X)
    (e : ComplexChart (m + 1) X) {K : Set (ComplexModel (m + 1))} (hK : MeasurableSet K)
    (hKe : K ⊆ e.val.target) (φ : testSpace (m + 1) X (m + 1))
    (hφ : ∀ x ∉ e.val.symm '' K,
      topRatio w.form.val (φ : SmoothRealForm (m + 1) X (2 * (m + 1))) x = 0) :
    integrationCurrent w φ =
      ∫ z in K, topDensity ((φ : SmoothRealForm (m + 1) X (2 * (m + 1))).coeff e z) := by
  rw [integrationCurrent_apply, ← setIntegral_eq_integral_of_forall_compl_eq_zero hφ,
    setIntegral_kahlerVolume_image w e hK hKe (continuous_topRatio w.isKahler.1 _)]
  refine setIntegral_congr_fun hK fun z hz => ?_
  have hzt := hKe hz
  rw [topRatio_eq_chartRatio w.isKahler.1 _ (e.val.map_target hzt), e.val.right_inv hzt,
    chartRatio]
  change volDensity w e z * (topDensity _ / volDensity w e z) = _
  field_simp [(volDensity_pos w e hzt).ne']

/-- The same, integrating over the whole model space, when the chart coefficient of `φ` vanishes
off `K` as well. -/
theorem integrationCurrent_apply_eq_integral (w : KahlerBackground (m + 1) X)
    (e : ComplexChart (m + 1) X) {K : Set (ComplexModel (m + 1))} (hK : MeasurableSet K)
    (hKe : K ⊆ e.val.target) (φ : testSpace (m + 1) X (m + 1))
    (hφ : ∀ x ∉ e.val.symm '' K,
      topRatio w.form.val (φ : SmoothRealForm (m + 1) X (2 * (m + 1))) x = 0)
    (hφK : ∀ z ∉ K, topDensity ((φ : SmoothRealForm (m + 1) X (2 * (m + 1))).coeff e z) = 0) :
    integrationCurrent w φ =
      ∫ z, topDensity ((φ : SmoothRealForm (m + 1) X (2 * (m + 1))).coeff e z) := by
  rw [integrationCurrent_apply_eq_setIntegral w e hK hKe φ hφ,
    setIntegral_eq_integral_of_forall_compl_eq_zero hφK]

end SGPT.Foundations.Analysis.Pending.IntegrationCurrentChart
