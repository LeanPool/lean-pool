/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IntegrationCurrent
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotPerm
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Smooth currents `[M] ∧ γ₁ ∧ ⋯ ∧ γ_p` and their trace measures

Let `(M, ω)` be a compact Kähler manifold of dimension `q + p` and `γ₀, …, γ_{p-1}` smooth closed
semipositive real `(1,1)`-forms.  The smooth current `[M] ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}` of bidimension
`(q, q)` is `φ ↦ [M](φ ∧ γ₀ ∧ ⋯ ∧ γ_{p-1})` (`smoothCurrent`, built on the integration current
`IntegrationCurrent.integrationCurrent`); it is positive.  Its trace measure
(`CurrentTraceMeasure.traceMeasure`, the measure `h ↦ T(h ωᵠ)`) is the project's global mixed
non-pluripolar measure of the slots `(ω, …, ω, γ₀, …, γ_{p-1})` with the potentials `0`
(`traceMeasure_smoothCurrent`), and, in the slot order `γ` first, of any family `θ` whose last
`q` slots are `ω` (`traceMeasure_smoothCurrent_eq_of_slots`).  So lower bounds for the mixed
measures `∫_{K ∩ V} α^p ∧ ω^q` (TN.4, step B3, TN-CLASSICAL) are lower bounds for the trace
measures of the currents `[M] ∧ α^p`, and they pass to weak limits by
`CurrentTraceMeasure.le_traceMeasure_of_tendsto` (`bou02-volume:4.12`, `dp04-kahler-cone:2.6`).
The interface was agreed on I-0831 (C-0003 to C-0005).

The two measure identities behind it are general:

* `traceMeasure_eq_withDensity` — if `T(h ωᵠ) = ∫ h R dV` for every chart-smooth `h`, with `R`
  continuous and `≥ 0` and `V` the Kähler volume, then `σ_T = R V` (finite measures on a compact
  manifold are determined by the integrals of chart-smooth functions,
  `measure_eq_of_integral_chartSmooth_eq`);
* `withDensity_topRatio_eq_globalMixedMeasure` — if the density of a top-degree form `Φ` is, in
  every chart, the mixed density of a family `θ` of semipositive forms, then `(Φ / ωⁿ) V` is the
  global mixed measure of `θ` with potentials `0` (`SmoothMixedMeasureDensity`).

## Main results

* `chainTestLM` (`φ ↦ φ ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}` on test forms), `chainTestLM_coeff`,
  `chainTestLM_mem_positiveCone`, `chainTestLM_smulTest`.
* `measure_eq_of_integral_chartSmooth_eq`, `traceMeasure_eq_withDensity`,
  `withDensity_topRatio_eq_globalMixedMeasure`.
* `smoothCurrent`, `isPositive_smoothCurrent`, `traceMeasure_smoothCurrent`,
  `mass_smoothCurrent`, `traceMeasure_smoothCurrent_eq_of_slots`.
* `smoothCurrentOf`, `isPositive_smoothCurrentOf`, `traceMeasure_smoothCurrentOf` — the same on a
  manifold of dimension `N` with `q + p = N`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SmoothCurrentTraceMeasure

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents CurrentTraceMeasure TopDegreeDensity IntegrationCurrent
  SmoothMixedMeasureDensity GlobalNonPluripolar

/-! ### Wedging test forms with finitely many `(1,1)`-forms -/

section Chain

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- `φ ↦ φ ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}` on test forms. -/
def chainTestLM : (p : ℕ) → (γ : Fin p → SmoothRealForm N M 2) → (∀ i, (γ i).IsTypeOneOne) →
    (q : ℕ) → testSpace N M q →ₗ[ℝ] testSpace N M (q + p)
  | 0, _, _, _ => LinearMap.id
  | p + 1, γ, hγ, q =>
      wedgeTestLM (hγ (Fin.last p)) (q + p) ∘ₗ
        chainTestLM p (fun i => γ i.castSucc) (fun i => hγ i.castSucc) q

theorem chainTestLM_succ_apply (p : ℕ) (γ : Fin (p + 1) → SmoothRealForm N M 2)
    (hγ : ∀ i, (γ i).IsTypeOneOne) (q : ℕ) (φ : testSpace N M q) :
    ((chainTestLM (p + 1) γ hγ q φ : testSpace N M (q + (p + 1))) :
        SmoothRealForm N M (2 * (q + (p + 1)))) =
      wedgeTwo ((chainTestLM p (fun i => γ i.castSucc) (fun i => hγ i.castSucc) q φ :
        testSpace N M (q + p)) : SmoothRealForm N M (2 * (q + p))) (γ (Fin.last p)) :=
  rfl

/-- **The coefficients of `φ ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}`**: if `φ` is pointwise the product of `α`, the
chain is pointwise the product of `α` followed by the `γⱼ`. -/
theorem chainTestLM_coeff : ∀ (p : ℕ) (γ : Fin p → SmoothRealForm N M 2)
    (hγ : ∀ i, (γ i).IsTypeOneOne) (q : ℕ) (φ : testSpace N M q) (e : ComplexChart N M)
    (z : ComplexModel N) {α : Fin q → RealForm N 2},
    (φ : SmoothRealForm N M (2 * q)).coeff e z = wedgeProd q α →
      ((chainTestLM p γ hγ q φ : testSpace N M (q + p)) :
          SmoothRealForm N M (2 * (q + p))).coeff e z =
        wedgeProd (q + p) (Fin.append α fun j => (γ j).coeff e z)
  | 0, γ, hγ, q, φ, e, z, α, hφ => by
    change (φ : SmoothRealForm N M (2 * q)).coeff e z = _
    rw [hφ, Fin.append_right_nil _ _ rfl]
    congr 1
  | p + 1, γ, hγ, q, φ, e, z, α, hφ => by
    rw [chainTestLM_succ_apply, wedgeTwo_coeff,
      chainTestLM_coeff p (fun i => γ i.castSucc) (fun i => hγ i.castSucc) q φ e z hφ,
      ← wedgeProd_snoc, ← Fin.append_snoc]
    congr 2
    exact Fin.snoc_init_self (fun j => (γ j).coeff e z)

/-- Wedging with semipositive `(1,1)`-forms keeps test forms strongly positive. -/
theorem chainTestLM_mem_positiveCone : ∀ (p : ℕ) (γ : Fin p → SmoothRealForm N M 2)
    (hγ : ∀ i, (γ i).IsTypeOneOne)
    (_ : ∀ i (e : ComplexChart N M) z, z ∈ e.val.target → IsSemipositiveOneOne ((γ i).coeff e z))
    (q : ℕ) {φ : testSpace N M q}, φ ∈ positiveCone N M q →
      chainTestLM p γ hγ q φ ∈ positiveCone N M (q + p)
  | 0, _, _, _, _, _, hφ => hφ
  | p + 1, γ, hγ, hγp, q, _, hφ => fun e z hz =>
    wedge_mem_spCone
      (chainTestLM_mem_positiveCone p (fun i => γ i.castSucc) (fun i => hγ i.castSucc)
        (fun i => hγp i.castSucc) q hφ e z hz) (hγp (Fin.last p) e z hz)

/-- The chain commutes with multiplication by a function. -/
theorem chainTestLM_smulTest : ∀ (p : ℕ) (γ : Fin p → SmoothRealForm N M 2)
    (hγ : ∀ i, (γ i).IsTypeOneOne) (q : ℕ) (h : M → ℝ) (hh : ChartSmooth (n := N) h)
    (φ : testSpace N M q),
    ((chainTestLM p γ hγ q (smulTest h hh φ) : testSpace N M (q + p)) :
        SmoothRealForm N M (2 * (q + p))) =
      smulFun h hh ((chainTestLM p γ hγ q φ : testSpace N M (q + p)) :
        SmoothRealForm N M (2 * (q + p)))
  | 0, _, _, _, _, _, _ => rfl
  | p + 1, γ, hγ, q, h, hh, φ => by
    rw [chainTestLM_succ_apply, chainTestLM_succ_apply,
      chainTestLM_smulTest p (fun i => γ i.castSucc) (fun i => hγ i.castSucc) q h hh φ,
      smulFun_wedgeTwo]

/-- The ratio `φ / ωⁿ` of a function multiple. -/
theorem topRatio_smulFun (w : SmoothRealForm N M 2) (h : M → ℝ) (hh : ChartSmooth (n := N) h)
    (Φ : SmoothRealForm N M (2 * N)) (x : M) :
    topRatio w (smulFun h hh Φ) x = h x * topRatio w Φ x := by
  simp only [topRatio, chartRatio, smulFun_coeff, topDensity_smul, mul_div_assoc]
  rw [(complexChartAt (n := N) x).val.left_inv (mem_complexChartAt_source x)]

end Chain

/-! ### Two measure identities -/

section Measures

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

theorem abs_integral_sub_le (μ : Measure M) [IsFiniteMeasure μ] (f g : C(M, ℝ)) :
    |∫ x, f x ∂μ - ∫ x, g x ∂μ| ≤ ‖f - g‖ * μ.real univ := by
  rw [← integral_sub (f.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)))
    (g.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))),
    ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
  simpa using (f - g).norm_coe_le_norm x

/-- **Finite measures on a compact complex manifold are determined by the integrals of
chart-smooth functions** (density of chart-smooth functions in `C(M, ℝ)`). -/
theorem measure_eq_of_integral_chartSmooth_eq {μ ν : Measure M} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ g : M → ℝ, ChartSmooth (n := N) g → ∫ x, g x ∂μ = ∫ x, g x ∂ν) : μ = ν := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  set F : C(M, ℝ) := f.toContinuousMap
  set C := μ.real univ + ν.real univ + 1 with hC
  have hCpos : 0 < C := by positivity
  have key : ∀ ε > 0, |∫ x, F x ∂μ - ∫ x, F x ∂ν| ≤ ε * C := by
    intro ε hε
    obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (chartSmoothSubalgebra N M) chartSmoothSubalgebra_separatesPoints F ε hε
    have hgs : ChartSmooth (n := N) ⇑(g : C(M, ℝ)) := g.2
    have e := h _ hgs
    have h1 := abs_integral_sub_le μ F g
    have h2 := abs_integral_sub_le ν F g
    have hFg : ‖F - (g : C(M, ℝ))‖ ≤ ε := by rw [norm_sub_rev]; exact hg.le
    have hμ : 0 ≤ μ.real univ := measureReal_nonneg
    have hν : 0 ≤ ν.real univ := measureReal_nonneg
    have h1' : |∫ x, F x ∂μ - ∫ x, (g : C(M, ℝ)) x ∂μ| ≤ ε * μ.real univ :=
      h1.trans (mul_le_mul_of_nonneg_right hFg hμ)
    have h2' : |∫ x, F x ∂ν - ∫ x, (g : C(M, ℝ)) x ∂ν| ≤ ε * ν.real univ :=
      h2.trans (mul_le_mul_of_nonneg_right hFg hν)
    rw [abs_le] at h1' h2' ⊢
    constructor <;> nlinarith [e]
  have hzero : |∫ x, F x ∂μ - ∫ x, F x ∂ν| = 0 := by
    by_contra hne
    have hpos : 0 < |∫ x, F x ∂μ - ∫ x, F x ∂ν| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have := key (|∫ x, F x ∂μ - ∫ x, F x ∂ν| / (2 * C)) (by positivity)
    have heq : |∫ x, F x ∂μ - ∫ x, F x ∂ν| / (2 * C) * C = |∫ x, F x ∂μ - ∫ x, F x ∂ν| / 2 := by
      field_simp
    rw [heq] at this
    linarith
  have := abs_eq_zero.mp hzero
  exact sub_eq_zero.mp this

/-- **The trace measure of a current given by a continuous density.** -/
theorem traceMeasure_eq_withDensity (w : KahlerBackground N M) {q : ℕ}
    (T : ProductCurrent N M q) (hT : IsPositive T) (R : M → ℝ) (hRc : Continuous R)
    (hR0 : ∀ x, 0 ≤ R x)
    (hval : ∀ (g : M → ℝ) (hg : ChartSmooth (n := N) g),
      T (smulTest g hg (kahlerTest w q)) = ∫ x, g x * R x ∂(kahlerVolume w)) :
    traceMeasure w T hT = (kahlerVolume w).withDensity (fun x => ENNReal.ofReal (R x)) := by
  have hRint : Integrable R (kahlerVolume w) :=
    hRc.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have : IsFiniteMeasure ((kahlerVolume w).withDensity fun x => ENNReal.ofReal (R x)) :=
    isFiniteMeasure_withDensity_ofReal hRint.2
  refine measure_eq_of_integral_chartSmooth_eq (N := N) fun g hg => ?_
  rw [integral_traceMeasure_chartSmooth w T hT g hg, hval g hg,
    integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (R x))
      (ENNReal.measurable_ofReal.comp hRc.measurable)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hR0 x), smul_eq_mul, mul_comm]

/-- **The smooth measure `(Φ / ωⁿ) ωⁿ` is a global mixed measure** as soon as the density of
`Φ` is, in every chart, the mixed density of a family of semipositive closed forms. -/
theorem withDensity_topRatio_eq_globalMixedMeasure (w : KahlerBackground N M)
    (Φ : SmoothRealForm N M (2 * N)) {θ : Fin N → ClosedRealOneOneForm N M}
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0))
    (hΦ : ∀ (e : ComplexChart N M) z, z ∈ e.val.target →
      topDensity (Φ.coeff e z) = actualMixedTopDensity fun i => (θ i).val.coeff e z) :
    (kahlerVolume w).withDensity (fun x => ENNReal.ofReal (topRatio w.form.val Φ x)) =
      globalMixedMeasure θ (fun _ _ => 0) hθ := by
  have hω : ∀ _ : Fin N, ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin N => w.form) (fun _ _ => 0) hω := rfl
  have hgm : Measurable fun x => ENNReal.ofReal (topRatio w.form.val Φ x) :=
    ENNReal.measurable_ofReal.comp (continuous_topRatio w.isKahler.1 Φ).measurable
  refine GlobalSlotStokes.measure_eq_of_restrict_eq_of_openCover
    (fun x : M => (complexChartAt (n := N) x).val.source)
    (fun x => (complexChartAt (n := N) x).val.open_source)
    (fun x => ⟨x, mem_complexChartAt_source x⟩) fun x => ?_
  set e := complexChartAt (n := N) x
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  set K := e.val.target ∩ e.val.symm ⁻¹' A with hKdef
  have hK : MeasurableSet K :=
    measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
      e.val.continuousOn_symm hA
  have hKe : K ⊆ e.val.target := inter_subset_left
  have himage : A ∩ e.val.source = e.val.symm '' K := by
    rw [hKdef, image_inter_preimage, e.val.symm_image_target_eq_source, inter_comm]
  rw [himage, withDensity_apply _ (measurableSet_chartSymm_image e hK hKe), hvol,
    setLIntegral_image_eq hω e hK hKe hgm, globalMixedMeasure_image_eq_lintegral hθ e hK hKe]
  refine setLIntegral_congr_fun hK fun z hz => ?_
  have hzt : z ∈ e.val.target := hKe hz
  have hx : e.val.symm z ∈ e.val.source := e.val.map_target hzt
  have hR : topRatio w.form.val Φ (e.val.symm z) = chartRatio w.form.val Φ e z := by
    rw [topRatio_eq_chartRatio w.isKahler.1 Φ hx, e.val.right_inv hzt]
  have hden : topDensity ((formPow w.form.val N).coeff e z) =
      actualMixedTopDensity fun _ : Fin N => w.form.val.coeff e z := by
    rw [formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]
  have hpos := topDensity_formPow_pos w.isKahler.1 hzt
  simp only [chartDensity]
  rw [hR, chartRatio, ← hden, ← ENNReal.ofReal_mul hpos.le, mul_div_cancel₀ _ hpos.ne',
    hΦ e z hzt]

end Measures

/-! ### The smooth currents `[M] ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}` -/

section SmoothCurrent

variable {q p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + p)) M]
  [IsComplexManifold (q + p) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The smooth current** `[M] ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}` of bidimension `(q, q)` on a compact Kähler
manifold of dimension `q + p`: `φ ↦ ∫_M φ ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}`. -/
def smoothCurrent (w : KahlerBackground (q + p) M) (γ : Fin p → ClosedRealOneOneForm (q + p) M) :
    ProductCurrent (q + p) M q :=
  integrationCurrent w ∘ₗ chainTestLM p (fun j => (γ j).val) (fun j => (γ j).2.2) q

theorem smoothCurrent_apply (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M) (φ : testSpace (q + p) M q) :
    smoothCurrent w γ φ =
      integrationCurrent w (chainTestLM p (fun j => (γ j).val) (fun j => (γ j).2.2) q φ) := rfl

/-- **The smooth current of semipositive forms is positive.** -/
theorem isPositive_smoothCurrent (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M)
    (hγ : ∀ j, ThetaPlurisubharmonic (γ j).val (fun _ => 0)) :
    IsPositive (smoothCurrent w γ) := fun _ hφ =>
  isPositive_integrationCurrent w _
    (chainTestLM_mem_positiveCone p _ _ (fun j _ _ hz => isSemipositiveOneOne_coeff (hγ j) hz)
      q hφ)

/-- The top-degree form `ωᵠ ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}` whose ratio to `ωⁿ` is the density of the trace
measure. -/
def traceForm (w : KahlerBackground (q + p) M) (γ : Fin p → ClosedRealOneOneForm (q + p) M) :
    testSpace (q + p) M (q + p) :=
  chainTestLM p (fun j => (γ j).val) (fun j => (γ j).2.2) q (kahlerTest w q)

theorem smoothCurrent_smulTest_kahlerTest (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M) (g : M → ℝ) (hg : ChartSmooth (n := q + p) g) :
    smoothCurrent w γ (smulTest g hg (kahlerTest w q)) =
      ∫ x, g x * topRatio w.form.val (traceForm w γ : SmoothRealForm (q + p) M (2 * (q + p))) x
        ∂(kahlerVolume w) := by
  rw [smoothCurrent_apply, integrationCurrent_apply, chainTestLM_smulTest]
  simp only [topRatio_smulFun]
  rfl

/-- The slots `(ω, …, ω, γ₀, …, γ_{p-1})`. -/
def slots (w : KahlerBackground (q + p) M) (γ : Fin p → ClosedRealOneOneForm (q + p) M) :
    Fin (q + p) → ClosedRealOneOneForm (q + p) M :=
  Fin.append (fun _ : Fin q => w.form) γ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem slots_thetaPlurisubharmonic (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M)
    (hγ : ∀ j, ThetaPlurisubharmonic (γ j).val (fun _ => 0)) :
    ∀ i, ThetaPlurisubharmonic (slots w γ i).val (fun _ => 0) := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [slots, Fin.append_left]
    exact ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  · rw [slots, Fin.append_right]
    exact hγ b

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem topDensity_traceForm (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M) (e : ComplexChart (q + p) M)
    (z : ComplexModel (q + p)) :
    topDensity ((traceForm w γ : SmoothRealForm (q + p) M (2 * (q + p))).coeff e z) =
      actualMixedTopDensity fun i => (slots w γ i).val.coeff e z := by
  have hφ : ((kahlerTest w q : testSpace (q + p) M q) : SmoothRealForm (q + p) M (2 * q)).coeff e
    z =
      wedgeProd q (fun _ => w.form.val.coeff e z) := by
    change (formPow w.form.val q).coeff e z = _
    rw [formPow_coeff, formPower_eq_wedgeProd]
  rw [traceForm, chainTestLM_coeff p _ _ q _ e z hφ, topDensity_wedgeProd]
  congr 1
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [slots, Fin.append_left]
  · simp only [slots, Fin.append_right]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem traceForm_mem_positiveCone (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M)
    (hγ : ∀ j, ThetaPlurisubharmonic (γ j).val (fun _ => 0)) :
    traceForm w γ ∈ positiveCone (q + p) M (q + p) :=
  chainTestLM_mem_positiveCone p _ _ (fun j _ _ hz => isSemipositiveOneOne_coeff (hγ j) hz) q
    (kahlerTest_mem_positiveCone w q)

/-- **The bridge**: the trace measure `([M] ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}) ∧ ωᵠ` is the global mixed
measure of the slots `(ω, …, ω, γ₀, …, γ_{p-1})` with the potentials `0`. -/
theorem traceMeasure_smoothCurrent (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M)
    (hγ : ∀ j, ThetaPlurisubharmonic (γ j).val (fun _ => 0)) :
    traceMeasure w (smoothCurrent w γ) (isPositive_smoothCurrent w γ hγ) =
      globalMixedMeasure (slots w γ) (fun _ _ => 0) (slots_thetaPlurisubharmonic w γ hγ) := by
  rw [traceMeasure_eq_withDensity w _ _ _ (continuous_topRatio w.isKahler.1 _)
      (topRatio_nonneg w.isKahler.1 (traceForm_mem_positiveCone w γ hγ))
      (smoothCurrent_smulTest_kahlerTest w γ)]
  exact withDensity_topRatio_eq_globalMixedMeasure w _ _
    fun e z _ => topDensity_traceForm w γ e z

/-- The mass of the smooth current is the total mixed mass of its slots. -/
theorem mass_smoothCurrent (w : KahlerBackground (q + p) M)
    (γ : Fin p → ClosedRealOneOneForm (q + p) M)
    (hγ : ∀ j, ThetaPlurisubharmonic (γ j).val (fun _ => 0)) :
    mass w (smoothCurrent w γ) =
      (globalMixedMeasure (slots w γ) (fun _ _ => 0) (slots_thetaPlurisubharmonic w γ hγ)).real
        univ := by
  rw [← traceMeasure_smoothCurrent w γ hγ, traceMeasure_real_univ]

/-- The slots `γ` first: the permutation `(ω-slots, γ-slots) ↦ (γ-slots, ω-slots)`. -/
def slotFlip (q p : ℕ) : Equiv.Perm (Fin (q + p)) :=
  finAddFlip.trans (finCongr (add_comm p q))

theorem slotFlip_castAdd (a : Fin q) :
    ((slotFlip q p (Fin.castAdd p a) : Fin (q + p)) : ℕ) = p + a := by
  simp only [slotFlip, Equiv.trans_apply, finAddFlip_apply_castAdd, finCongr_apply, Fin.val_cast,
    Fin.val_natAdd]

theorem slotFlip_natAdd (b : Fin p) :
    ((slotFlip q p (Fin.natAdd q b) : Fin (q + p)) : ℕ) = b := by
  simp only [slotFlip, Equiv.trans_apply, finAddFlip_apply_natAdd, finCongr_apply, Fin.val_cast,
    Fin.val_castAdd]

omit [BorelSpace M] in
theorem globalMixedMeasure_congr {θ θ' : Fin (q + p) → ClosedRealOneOneForm (q + p) M}
    (h : θ = θ') (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0))
    (hθ' : ∀ i, ThetaPlurisubharmonic (θ' i).val (fun _ => 0)) :
    globalMixedMeasure θ (fun _ _ => 0) hθ = globalMixedMeasure θ' (fun _ _ => 0) hθ' := by
  subst h
  rfl

/-- **The bridge, slots `γ` first** (the order of TN.4 step B3): for a family `θ` of smooth
semipositive closed forms whose slots `p, …, q + p - 1` are `ω`, the trace measure of
`[M] ∧ θ₀ ∧ ⋯ ∧ θ_{p-1}` is the global mixed measure of `θ` with the potentials `0`. -/
theorem traceMeasure_smoothCurrent_eq_of_slots (w : KahlerBackground (q + p) M)
    (θ : Fin (q + p) → ClosedRealOneOneForm (q + p) M)
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0))
    (hω : ∀ i : Fin (q + p), p ≤ (i : ℕ) → θ i = w.form) :
    traceMeasure w (smoothCurrent w fun j : Fin p => θ (Fin.castLE (Nat.le_add_left p q) j))
        (isPositive_smoothCurrent w _ fun _ => hθ _) =
      globalMixedMeasure θ (fun _ _ => 0) hθ := by
  rw [traceMeasure_smoothCurrent w _ fun _ => hθ _]
  have hperm : slots w (fun j : Fin p => θ (Fin.castLE (Nat.le_add_left p q) j)) =
      fun i => θ (slotFlip q p i) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · rw [slots, Fin.append_left]
      refine (hω _ ?_).symm
      rw [slotFlip_castAdd]
      exact Nat.le_add_right p a
    · rw [slots, Fin.append_right]
      congr 1
      exact Fin.ext (by rw [slotFlip_natAdd]; rfl)
  rw [globalMixedMeasure_congr hperm _ (fun i => hθ (slotFlip q p i))]
  exact GlobalSlotPerm.globalMixedMeasure_perm hθ (slotFlip q p)

end SmoothCurrent

/-! ### On a manifold of dimension `N = q + p` -/

section General

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The smooth current `[M] ∧ γ₀ ∧ ⋯ ∧ γ_{p-1}` of bidimension `(q, q)` on a compact Kähler
manifold of dimension `N = q + p`. -/
def smoothCurrentOf (w : KahlerBackground N M) {q p : ℕ} (h : q + p = N)
    (γ : Fin p → ClosedRealOneOneForm N M) : ProductCurrent N M q := by
  subst h
  exact smoothCurrent w γ

theorem isPositive_smoothCurrentOf (w : KahlerBackground N M) {q p : ℕ} (h : q + p = N)
    (γ : Fin p → ClosedRealOneOneForm N M)
    (hγ : ∀ j, ThetaPlurisubharmonic (γ j).val (fun _ => 0)) :
    IsPositive (smoothCurrentOf w h γ) := by
  subst h
  exact isPositive_smoothCurrent w γ hγ

/-- **The bridge on a manifold of dimension `N = q + p`, slots `γ` first.** -/
theorem traceMeasure_smoothCurrentOf (w : KahlerBackground N M) {q p : ℕ} (h : q + p = N)
    (θ : Fin N → ClosedRealOneOneForm N M)
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0))
    (hω : ∀ i : Fin N, p ≤ (i : ℕ) → θ i = w.form) :
    traceMeasure w (smoothCurrentOf w h fun j : Fin p => θ (Fin.castLE (by omega) j))
        (isPositive_smoothCurrentOf w h _ fun _ => hθ _) =
      globalMixedMeasure θ (fun _ _ => 0) hθ := by
  subst h
  exact traceMeasure_smoothCurrent_eq_of_slots w θ hθ hω

/-- The mass of `[M] ∧ θ₀ ∧ ⋯ ∧ θ_{p-1}` is the total mixed mass of `θ`. -/
theorem mass_smoothCurrentOf (w : KahlerBackground N M) {q p : ℕ} (h : q + p = N)
    (θ : Fin N → ClosedRealOneOneForm N M)
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0))
    (hω : ∀ i : Fin N, p ≤ (i : ℕ) → θ i = w.form) :
    mass w (smoothCurrentOf w h fun j : Fin p => θ (Fin.castLE (by omega) j)) =
      (globalMixedMeasure θ (fun _ _ => 0) hθ).real univ := by
  rw [← traceMeasure_smoothCurrentOf w h θ hθ hω, traceMeasure_real_univ]

end General

end SGPT.Foundations.Analysis.Pending.SmoothCurrentTraceMeasure
