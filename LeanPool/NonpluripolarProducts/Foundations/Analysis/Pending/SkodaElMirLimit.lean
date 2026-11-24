/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CurrentRestriction

/-!
# The restriction `𝟙_E T` as a limit of `T (U_k φ)`

Let `T` be a positive current of bidimension `(q, q)` on a compact complex manifold with a Kähler
form `ω`, and `φ` a test form.  With `c ≥ 0` such that `c ω^q + φ` is positive,
`T (U φ) = ∫ U d(T ∧ (c ω^q + φ)) - c ∫ U dσ_T` for every chart-smooth `U`
(`apply_smulTest_eq`): the signed measure `T ∧ φ = T ∧ (c ω^q + φ) - c σ_T` integrates `U`.

* **Locality** (`restrictCurrent_eq_setIntegral`): if `h ≤ 1` is chart-smooth and `h φ = φ`
  at every chart point, then `(1 - h)(T ∧ φ) = 0`, so
  `𝟙_E T (φ) = ∫_E h d(T ∧ (c ω^q + φ)) - c ∫_E h dσ_T`.
* **Dominated convergence** (`tendsto_apply_smulTest`): if moreover `U_k` are chart-smooth,
  uniformly bounded, and `U_k → 𝟙_E h` pointwise, then `T (U_k φ) → 𝟙_E T (φ)`.

This is steps (E1)--(E2) of the Skoda--El Mir argument for the diagonal (`demailly-cadg:III.2.3`,
TN.4 step B4.3): the cut-offs `U_k` are only
defined near the support of `φ`, which is why `h` is there.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.SkodaElMirLimit

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents CurrentTraceMeasure SmoothCurrentTraceMeasure
  CurrentRestriction

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) (hT : IsPositive T)

/-- **`T (U φ)` is the integral of `U` against the signed measure `T ∧ φ`.** -/
theorem apply_smulTest_eq (φ : testSpace n M q) {c : ℝ}
    (hc : c • kahlerTest w q + φ ∈ positiveCone n M q) {U : M → ℝ}
    (hU : ChartSmooth (n := n) U) :
    T (smulTest U hU φ) =
      ∫ x, U x ∂(testMeasure w T hT _ hc) - c * ∫ x, U x ∂(traceMeasure w T hT) := by
  rw [integral_testMeasure w T hT _ hc U hU, integral_traceMeasure_chartSmooth w T hT U hU,
    smulTest_add_right, map_add]
  have : smulTest U hU (c • kahlerTest w q) = c • smulTest U hU (kahlerTest w q) :=
    Subtype.ext (smoothRealForm_ext fun _ _ => smul_comm _ _ _)
  rw [this, map_smul, smul_eq_mul]
  ring

omit [CompactSpace M] in
theorem measureReal_withDensity_ofReal (μ : Measure M) {F : M → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) {E : Set M} (hE : MeasurableSet E) :
    (μ.withDensity fun x => ENNReal.ofReal (F x)).real E = ∫ x in E, F x ∂μ := by
  rw [measureReal_def, withDensity_apply _ hE,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hF.aestronglyMeasurable]

omit [CompactSpace M] in
theorem integral_withDensity_ofReal (μ : Measure M) {F : M → ℝ}
    (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x) (g : M → ℝ) :
    ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (F x)) = ∫ x, F x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (F x))
      (ENNReal.measurable_ofReal.comp hF.measurable)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hF0 x), smul_eq_mul]

/-- **Locality of the signed measure `T ∧ φ`**: if `0 ≤ h ≤ 1` is chart-smooth and `h φ = φ` at
every chart point, then `𝟙_E T (φ) = ∫_E h d(T ∧ (c ω^q + φ)) - c ∫_E h dσ_T` (only `h ≤ 1` is
used: `(1 - h)(T ∧ (c ω^q + φ)) = c (1 - h) σ_T` as positive measures). -/
theorem restrictCurrent_eq_setIntegral {E : Set M} (hE : MeasurableSet E) (φ : testSpace n M q)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c • kahlerTest w q + φ ∈ positiveCone n M q)
    {h : M → ℝ} (hh : ChartSmooth (n := n) h) (h1 : ∀ x, h x ≤ 1)
    (hφ : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      h (e.val.symm z) • (φ : SmoothRealForm n M (2 * q)).coeff e z =
        (φ : SmoothRealForm n M (2 * q)).coeff e z) :
    restrictCurrent w T hT E φ =
      ∫ x in E, h x ∂(testMeasure w T hT _ hc) - c * ∫ x in E, h x ∂(traceMeasure w T hT) := by
  set μ := testMeasure w T hT _ hc with hμ
  set σ := traceMeasure w T hT with hσ
  set k : M → ℝ := fun x => 1 - h x with hk_def
  have hk : ChartSmooth (n := n) k := fun e => contDiffOn_const.sub (hh e)
  have hkc : Continuous k := chartSmooth_continuous hk
  have hk0 : ∀ x, 0 ≤ k x := fun x => sub_nonneg.mpr (h1 x)
  have hck0 : ∀ x, 0 ≤ c * k x := fun x => mul_nonneg hc0 (hk0 x)
  -- `(1 - h) φ = 0`
  have hkill : ∀ (g : M → ℝ) (hg : ChartSmooth (n := n) g),
      T (smulTest (fun x => g x * k x) (chartSmooth_mul hg hk) φ) = 0 := by
    intro g hg
    refine hT.apply_eq_zero_of_coeff_eqOn_zero fun e z hz => ?_
    change (g (e.val.symm z) * (1 - h (e.val.symm z))) •
        (φ : SmoothRealForm n M (2 * q)).coeff e z = 0
    have hsub : (1 - h (e.val.symm z)) • (φ : SmoothRealForm n M (2 * q)).coeff e z = 0 := by
      have hv := hφ e z hz
      ext v
      have hv' := congrArg (fun B : RealForm n (2 * q) => B v) hv
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hv' ⊢
      rw [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, sub_mul, one_mul]
      linarith
    rw [mul_smul, hsub, smul_zero]
  have hfin1 : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (k x)) :=
    isFiniteMeasure_withDensity_ofReal (integrable_of_chartSmooth μ hk).2
  have hfin2 : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (c * k x)) :=
    isFiniteMeasure_withDensity_ofReal
      (integrable_of_chartSmooth σ (n := n) (fun e => contDiffOn_const.mul (hk e))).2
  have heq : (μ.withDensity fun x => ENNReal.ofReal (k x)) =
      σ.withDensity fun x => ENNReal.ofReal (c * k x) := by
    refine measure_eq_of_integral_chartSmooth_eq (N := n) fun g hg => ?_
    rw [integral_withDensity_ofReal μ hkc hk0,
      integral_withDensity_ofReal σ (F := fun x => c * k x) (continuous_const.mul hkc) hck0]
    have h1' := apply_smulTest_eq w T hT φ hc (chartSmooth_mul hg hk)
    rw [hkill g hg] at h1'
    have e1 : ∫ x, k x * g x ∂μ = ∫ x, g x * k x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have e2 : ∫ x, c * k x * g x ∂σ = c * ∫ x, g x * k x ∂σ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [e1, e2]
    linarith
  have hE' : (μ.withDensity fun x => ENNReal.ofReal (k x)).real E =
      (σ.withDensity fun x => ENNReal.ofReal (c * k x)).real E := by rw [heq]
  rw [measureReal_withDensity_ofReal μ hkc hk0 hE,
    measureReal_withDensity_ofReal σ (F := fun x => c * k x) (continuous_const.mul hkc) hck0 hE]
    at hE'
  have hhi : ∀ ν : Measure M, IsFiniteMeasure ν → IntegrableOn h E ν := fun ν _ =>
    (integrable_of_chartSmooth ν hh).integrableOn
  rw [restrictCurrent_apply w T hT E φ hc0 hc]
  have i1 : ∫ x in E, k x ∂μ = μ.real E - ∫ x in E, h x ∂μ := by
    rw [hk_def, integral_sub (integrable_const 1) (hhi μ inferInstance), setIntegral_const,
      smul_eq_mul, mul_one]
  have i2 : ∫ x in E, c * k x ∂σ = c * (σ.real E - ∫ x in E, h x ∂σ) := by
    rw [integral_const_mul, hk_def, integral_sub (integrable_const 1) (hhi σ inferInstance),
      setIntegral_const, smul_eq_mul, mul_one]
  rw [i1, i2] at hE'
  linarith

/-- **`T (U_k φ) → 𝟙_E T (φ)`** for uniformly bounded chart-smooth `U_k → 𝟙_E h`, when
`h ≤ 1` and `h φ = φ` at every chart point (dominated convergence for the two positive
measures making up `T ∧ φ`). -/
theorem tendsto_apply_smulTest {E : Set M} (hE : MeasurableSet E) (φ : testSpace n M q)
    {h : M → ℝ} (hh : ChartSmooth (n := n) h) (h1 : ∀ x, h x ≤ 1)
    (hφ : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      h (e.val.symm z) • (φ : SmoothRealForm n M (2 * q)).coeff e z =
        (φ : SmoothRealForm n M (2 * q)).coeff e z)
    {U : ℕ → M → ℝ} (hU : ∀ k, ChartSmooth (n := n) (U k)) {C : ℝ}
    (hUC : ∀ k x, |U k x| ≤ C) (hlim : ∀ x, Tendsto (fun k => U k x) atTop (𝓝 (E.indicator h x))) :
    Tendsto (fun k => T (smulTest (U k) (hU k) φ)) atTop (𝓝 (restrictCurrent w T hT E φ)) := by
  have hc0 := restrictConst_nonneg w φ
  have hc := restrictConst_add w φ
  rw [restrictCurrent_eq_setIntegral w T hT hE φ hc0 hc hh h1 hφ]
  have hform : (fun k => T (smulTest (U k) (hU k) φ)) = fun k =>
      ∫ x, U k x ∂(testMeasure w T hT _ hc) -
        restrictConst w φ * ∫ x, U k x ∂(traceMeasure w T hT) :=
    funext fun k => apply_smulTest_eq w T hT φ hc (hU k)
  rw [hform]
  have hdc : ∀ ν : Measure M, IsFiniteMeasure ν →
      Tendsto (fun k => ∫ x, U k x ∂ν) atTop (𝓝 (∫ x in E, h x ∂ν)) := by
    intro ν _
    rw [← integral_indicator hE]
    exact tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun k => (chartSmooth_continuous (hU k)).aestronglyMeasurable) (integrable_const C)
      (fun k => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hUC k x)
      (Eventually.of_forall hlim)
  exact (hdc _ inferInstance).sub ((hdc _ inferInstance).const_mul _)

end SGPT.Foundations.Analysis.Pending.SkodaElMirLimit
