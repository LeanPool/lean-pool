/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IntegrationCurrent

/-!
# Positive currents of top bidimension are measures

On a compact complex manifold `M` of dimension `n` with a Kähler form `ω`, a test form of top
degree `2n` is `φ = (φ / ωⁿ) ωⁿ` pointwise (`topForm_eq_smul`: top-degree real forms on `ℂⁿ` form
a line), and the ratio `φ / ωⁿ` (`IntegrationCurrent.topRatio`) is chart-smooth
(`chartSmooth_topRatio`).  Hence a positive current `S` of bidimension `(n, n)` is integration
of the ratio against its trace measure (`apply_eq_integral_topRatio`):

`S φ = ∫ φ / ωⁿ dσ_S`,

and two such currents with the same trace measure coincide.  This reduces step (S4) of the
support theorem (TN.4 step B4.4, `bou:diagonal-support`: a closed positive current of top
bidimension on a connected compact `X` is a multiple of `[X]`) to a statement on measures.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.TopBidimensionCurrents

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents TopDegreeDensity CurrentTraceMeasure IntegrationCurrent

section Line

variable {n : ℕ}

/-- **Top-degree real forms form a line**: `A = (A / W) W` when the density of `W` is nonzero. -/
theorem topForm_eq_smul (A W : RealForm n (2 * n)) (hW : topDensity W ≠ 0) :
    A = (topDensity A / topDensity W) • W := by
  have hA := (A.toAlternatingMap).eq_smul_basis_det (topBasis n)
  have hW' := (W.toAlternatingMap).eq_smul_basis_det (topBasis n)
  ext v
  have h1 := congrArg (fun f => f v) hA
  have h2 := congrArg (fun f => f v) hW'
  simp only [_root_.smul_apply, smul_eq_mul, ContinuousAlternatingMap.coe_toAlternatingMap]
    at h1 h2
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  change A v = A (topBasis n) / W (topBasis n) * W v
  change W (topBasis n) ≠ 0 at hW
  rw [h1, h2]
  field_simp

end Line

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The ratio `φ / ωⁿ` is chart-smooth.** -/
theorem chartSmooth_topRatio {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    (φ : SmoothRealForm n M (2 * n)) : ChartSmooth (n := n) (topRatio w φ) := by
  intro e
  have := realForm_finiteDimensional (n := n) (2 * n)
  have hnum : ContDiffOn ℝ ∞ (fun z => topDensity (φ.coeff e z)) e.val.target :=
    (topDensityLM (n := n)).toContinuousLinearMap.contDiff.comp_contDiffOn (φ.smooth e)
  have hden : ContDiffOn ℝ ∞ (fun z => topDensity ((formPow w n).coeff e z)) e.val.target :=
    (topDensityLM (n := n)).toContinuousLinearMap.contDiff.comp_contDiffOn ((formPow w n).smooth e)
  refine (hnum.div hden fun z hz => (topDensity_formPow_pos hw hz).ne').congr fun z hz => ?_
  rw [topRatio_eq_chartRatio hw φ (e.val.map_target hz), e.val.right_inv hz]
  rfl

/-- **`φ = (φ / ωⁿ) ωⁿ` at every chart point.** -/
theorem coeff_eq_topRatio_smul {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    (φ : SmoothRealForm n M (2 * n)) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    φ.coeff e z = topRatio w φ (e.val.symm z) • (formPow w n).coeff e z := by
  rw [topRatio_eq_chartRatio hw φ (e.val.map_target hz), e.val.right_inv hz, chartRatio]
  exact topForm_eq_smul _ _ (topDensity_formPow_pos hw hz).ne'

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **A positive current of top bidimension is integration of `φ / ωⁿ` against its trace
measure.** -/
theorem apply_eq_integral_topRatio (w : KahlerBackground n M) {S : ProductCurrent n M n}
    (hS : IsPositive S) (φ : testSpace n M n) :
    S φ = ∫ x, topRatio w.form.val (φ : SmoothRealForm n M (2 * n)) x ∂(traceMeasure w S hS) := by
  have hr := chartSmooth_topRatio w.isKahler.1 (φ : SmoothRealForm n M (2 * n))
  rw [integral_traceMeasure_chartSmooth w S hS _ hr]
  refine hS.apply_eq_of_coeff_eqOn fun e z hz => ?_
  rw [coeff_eq_topRatio_smul w.isKahler.1 _ e hz]
  rfl

/-- **Positive currents of top bidimension with proportional trace measures are proportional.** -/
theorem eq_smul_integrationCurrent (w : KahlerBackground n M) {S : ProductCurrent n M n}
    (hS : IsPositive S) {c : ℝ} (hc : 0 ≤ c)
    (hσ : traceMeasure w S hS = ENNReal.ofReal c • kahlerVolume w) :
    S = c • integrationCurrent w := by
  ext φ
  rw [apply_eq_integral_topRatio w hS φ, hσ, integral_smul_measure, ENNReal.toReal_ofReal hc,
    LinearMap.smul_apply, integrationCurrent_apply, smul_eq_mul]

end SGPT.Foundations.Analysis.Pending.TopBidimensionCurrents
