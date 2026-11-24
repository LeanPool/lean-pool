/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TopDegreeDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CurrentTraceMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DiagonalMass
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalPotentials

/-!
# The integration current of a compact Kähler manifold

Let `(M, ω)` be a compact complex manifold of dimension `n` with a Kähler form `ω`.  A smooth
real form `φ` of top degree `2n` is, in every chart, a multiple of the Euclidean volume form,
and so is `ωⁿ`; the ratio `φ / ωⁿ` of the two densities
(`TopDegreeDensity.topDensity`) does not depend on the chart, because both densities are
multiplied by the same Jacobian determinant under a change of coordinates
(`chartRatio_transition`).  It is a continuous function `topRatio ω φ` on `M`.

The *integration current* is `[M] φ = ∫_M φ = ∫_M (φ / ωⁿ) ωⁿ`, where the measure `ωⁿ` is the
project's Kähler volume: the non-pluripolar Monge--Ampère measure of the potential `0` in the
class of `ω`, `DiagonalMass.diagonalPotentialMeasure ω 0` (`kahlerVolume`).  It is a current of
bidimension `(n, n)` in the sense of `Pending.PositiveProductCurrents` (a linear functional on
the top-degree test forms), it is positive because strongly positive top-degree forms have
nonnegative density (`TopDegreeDensity.topDensity_nonneg_of_mem_spCone`), and its mass is the
volume `∫_M ωⁿ` (`mass_integrationCurrent`).  This is the current `[M]` of
`demailly-cadg:III.1` (Example 1.20 with `Z = M`), and wedging it with smooth semipositive
`(1,1)`-forms gives the smooth closed positive currents `[M] ∧ γ₁ ∧ ⋯ ∧ γ_p` used by
`bou02-volume:4.12` / `dp04-kahler-cone:2.6` (TN.4 plan, step B2).

## Main results

* `chartRatio`, `chartRatio_transition` — the density ratio and its chart independence.
* `topRatio`, `topRatio_eq_chartRatio`, `continuous_topRatio`, `topRatio_add`,
  `topRatio_smul`, `topRatio_formPow`, `topRatio_nonneg`.
* `kahlerVolume` (finite), `integrationCurrent`, `integrationCurrent_apply`,
  `isPositive_integrationCurrent`, `mass_integrationCurrent`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.IntegrationCurrent

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents TopDegreeDensity

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### The density ratio `φ / ωⁿ` -/

section Ratio

/-- The ratio `φ / ωⁿ` of the densities of a top-degree form and of the `n`-th power of a
two-form, read in a chart. -/
def chartRatio (w : SmoothRealForm n M 2) (φ : SmoothRealForm n M (2 * n))
    (e : ComplexChart n M) (z : ComplexModel n) : ℝ :=
  topDensity (φ.coeff e z) / topDensity ((formPow w n).coeff e z)

/-- The coefficient of a form in one chart is the pullback of its coefficient in another. -/
theorem coeff_eq_compContinuousLinearMap {k : ℕ} (φ : SmoothRealForm n M k)
    {e f : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ (chartTransition e f).source) :
    φ.coeff e z = (φ.coeff f (chartTransition e f z)).compContinuousLinearMap
      (chartTransitionDerivative e f z) := by
  ext v
  exact φ.compatible e f z hz v

/-- The Jacobian law for the density of a top-degree form under a change of charts. -/
theorem topDensity_coeff_transition (φ : SmoothRealForm n M (2 * n))
    {e f : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ (chartTransition e f).source) :
    topDensity (φ.coeff e z) =
      LinearMap.det (chartTransitionDerivative e f z :
        ComplexModel n →ₗ[ℝ] ComplexModel n) *
        topDensity (φ.coeff f (chartTransition e f z)) := by
  rw [coeff_eq_compContinuousLinearMap φ hz, topDensity_compContinuousLinearMap]

omit [IsComplexManifold n M] in
theorem mem_target_of_mem_chartTransition_source {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source) : z ∈ e.val.target := by
  have h := hz
  simp only [chartTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source] at h
  exact h.1

/-- The density of `ωⁿ` is positive on chart targets for a Hermitian form `ω`. -/
theorem topDensity_formPow_pos {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target) :
    0 < topDensity ((formPow w n).coeff e z) := by
  rw [formPow_coeff]
  exact topDensity_formPower_pos (hw e z hz).1 (hw e z hz).2

/-- **The ratio does not depend on the chart.** -/
theorem chartRatio_transition {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    (φ : SmoothRealForm n M (2 * n)) {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source) :
    chartRatio w φ e z = chartRatio w φ f (chartTransition e f z) := by
  set d := LinearMap.det (chartTransitionDerivative e f z :
    ComplexModel n →ₗ[ℝ] ComplexModel n)
  have hnum := topDensity_coeff_transition φ hz
  have hden := topDensity_coeff_transition (formPow w n) hz
  have hpos := topDensity_formPow_pos hw (mem_target_of_mem_chartTransition_source hz)
  have hd : d ≠ 0 := by
    intro h0
    rw [hden] at hpos
    change 0 < d * _ at hpos
    rw [h0, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  rw [chartRatio, chartRatio, hnum, hden, mul_div_mul_left _ _ hd]

/-- The ratio `φ / ωⁿ` at a point of `M`, read in the preferred chart. -/
def topRatio (w : SmoothRealForm n M 2) (φ : SmoothRealForm n M (2 * n)) (x : M) : ℝ :=
  chartRatio w φ (complexChartAt x) ((complexChartAt (n := n) x).val x)

/-- The ratio may be read in any chart around the point. -/
theorem topRatio_eq_chartRatio {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    (φ : SmoothRealForm n M (2 * n)) {e : ComplexChart n M} {x : M} (hx : x ∈ e.val.source) :
    topRatio w φ x = chartRatio w φ e (e.val x) := by
  set f := complexChartAt (n := n) x
  have hz : e.val x ∈ (chartTransition e f).source := by
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
    refine ⟨e.val.map_source hx, ?_⟩
    rw [e.val.left_inv hx]
    exact mem_complexChartAt_source x
  have htr : chartTransition e f (e.val x) = f.val x := by
    simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    rw [e.val.left_inv hx]
  rw [chartRatio_transition hw φ hz, htr]
  rfl

/-- The ratio is continuous on the source of every chart, hence on `M`. -/
theorem continuousOn_chartRatio {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    (φ : SmoothRealForm n M (2 * n)) (e : ComplexChart n M) :
    ContinuousOn (fun x => chartRatio w φ e (e.val x)) e.val.source := by
  have hmaps : MapsTo e.val e.val.source e.val.target := fun x hx => e.val.map_source hx
  have hnum : ContinuousOn (fun x => topDensity (φ.coeff e (e.val x))) e.val.source :=
    continuous_topDensity.comp_continuousOn
      ((φ.smooth e).continuousOn.comp e.val.continuousOn hmaps)
  have hden : ContinuousOn (fun x => topDensity ((formPow w n).coeff e (e.val x)))
      e.val.source :=
    continuous_topDensity.comp_continuousOn
      (((formPow w n).smooth e).continuousOn.comp e.val.continuousOn hmaps)
  exact hnum.div hden fun x hx => (topDensity_formPow_pos hw (hmaps hx)).ne'

theorem continuous_topRatio {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    (φ : SmoothRealForm n M (2 * n)) : Continuous (topRatio w φ) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  set e := complexChartAt (n := n) x₀
  have hsrc : e.val.source ∈ 𝓝 x₀ := e.val.open_source.mem_nhds (mem_complexChartAt_source x₀)
  have hcont := (continuousOn_chartRatio hw φ e).continuousAt hsrc
  refine hcont.congr ?_
  filter_upwards [hsrc] with x hx
  exact (topRatio_eq_chartRatio hw φ hx).symm

theorem topRatio_add (w : SmoothRealForm n M 2) (φ ψ : SmoothRealForm n M (2 * n)) (x : M) :
    topRatio w (φ + ψ) x = topRatio w φ x + topRatio w ψ x := by
  simp only [topRatio, chartRatio, coeff_add, topDensity_add, add_div]

theorem topRatio_smul (w : SmoothRealForm n M 2) (c : ℝ) (φ : SmoothRealForm n M (2 * n))
    (x : M) : topRatio w (c • φ) x = c * topRatio w φ x := by
  simp only [topRatio, chartRatio, coeff_smul, topDensity_smul, mul_div_assoc]

theorem topRatio_formPow {w : SmoothRealForm n M 2} (hw : w.IsHermitian) (x : M) :
    topRatio w (formPow w n) x = 1 :=
  div_self (topDensity_formPow_pos hw
    ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))).ne'

/-- The ratio of a strongly positive test form is nonnegative. -/
theorem topRatio_nonneg {w : SmoothRealForm n M 2} (hw : w.IsHermitian)
    {φ : testSpace n M n} (hφ : φ ∈ positiveCone n M n) (x : M) :
    0 ≤ topRatio w (φ : SmoothRealForm n M (2 * n)) x := by
  have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  exact div_nonneg (topDensity_nonneg_of_mem_spCone (hφ _ _ hz))
    (topDensity_formPow_pos hw hz).le

end Ratio

/-! ### The integration current -/

section Current

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The Kähler volume `ωⁿ`: the non-pluripolar measure of the potential `0` in the class of
`ω`. -/
def kahlerVolume (w : KahlerBackground n M) : Measure M :=
  DiagonalMass.diagonalPotentialMeasure w.form (fun _ => 0)
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive)

instance (w : KahlerBackground n M) : IsFiniteMeasure (kahlerVolume w) :=
  GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure w fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1

theorem integrable_topRatio (w : KahlerBackground n M) (φ : SmoothRealForm n M (2 * n)) :
    Integrable (topRatio w.form.val φ) (kahlerVolume w) :=
  (continuous_topRatio w.isKahler.1 φ).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

/-- **The integration current** `[M] φ = ∫_M φ = ∫_M (φ / ωⁿ) ωⁿ` on top-degree test forms. -/
def integrationCurrent (w : KahlerBackground n M) : ProductCurrent n M n where
  toFun φ := ∫ x, topRatio w.form.val (φ : SmoothRealForm n M (2 * n)) x ∂(kahlerVolume w)
  map_add' φ ψ := by
    simp only [Submodule.coe_add, topRatio_add]
    exact integral_add (integrable_topRatio w _) (integrable_topRatio w _)
  map_smul' c φ := by
    simp only [Submodule.coe_smul, topRatio_smul, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c _

theorem integrationCurrent_apply (w : KahlerBackground n M) (φ : testSpace n M n) :
    integrationCurrent w φ =
      ∫ x, topRatio w.form.val (φ : SmoothRealForm n M (2 * n)) x ∂(kahlerVolume w) := rfl

/-- **The integration current is positive.** -/
theorem isPositive_integrationCurrent (w : KahlerBackground n M) :
    IsPositive (integrationCurrent w) := fun _ hφ =>
  integral_nonneg fun x => topRatio_nonneg w.isKahler.1 hφ x

/-- **The mass of `[M]` is the volume** `∫_M ωⁿ`. -/
theorem mass_integrationCurrent (w : KahlerBackground n M) :
    mass w (integrationCurrent w) = (kahlerVolume w).real univ := by
  rw [mass, integrationCurrent_apply]
  change ∫ x, topRatio w.form.val (formPow w.form.val n) x ∂(kahlerVolume w) = _
  simp only [topRatio_formPow w.isKahler.1, integral_const, smul_eq_mul, mul_one]

end Current

end SGPT.Foundations.Analysis.Pending.IntegrationCurrent
