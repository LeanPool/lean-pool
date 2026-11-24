/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothCurrentTraceMeasure

/-!
# Restriction of a positive current to a Borel set

Let `T` be a positive current of bidimension `(q, q)` on a compact complex manifold `M` with a
Kähler form `ω` (`PositiveProductCurrents`).  For a positive test form `ψ` the functional
`h ↦ T (h ψ)` on chart-smooth functions is positive; it is the `(0,0)`-current
`testCurrent T ψ`, and its trace measure is a finite Borel measure `T ∧ ψ` (`testMeasure`) with
`∫ h d(T ∧ ψ) = T (h ψ)`.  These measures are additive and positively homogeneous in `ψ`,
`T ∧ ω^q = σ_T` is the trace measure, and `T ∧ ψ ≤ c σ_T` when `c ω^q - ψ` is positive.

Every test form `φ` has `c ≥ 0` with `c ω^q ± φ` positive (`ω^q` is an order unit), so
`T ∧ φ := T ∧ (c ω^q + φ) - c σ_T` is a finite signed measure, independent of `c`.  The
*restriction* `𝟙_E T (φ) = (T ∧ φ)(E)` (`restrictCurrent`, `demailly-cadg:III.1.14`, `III.2.4`)
is a positive current with mass `σ_T(E)`, `T = 𝟙_E T + 𝟙_{M \ E} T` for measurable `E`,
`𝟙_E T = 0` when `σ_T(E) = 0`, `𝟙_E T (h ψ) = ∫_E h d(T ∧ ψ)`, and the trace measure of
`𝟙_E T` is `σ_T` restricted to `E`.  This is step B4.2 of the TN.4 plan for Boucksom's
criterion (design D3 of the Skoda–El Mir extension argument; blueprint
`bou:current-restriction`).

## Main results

* `zeroFun` (smooth `0`-forms are chart-smooth functions), `functionTestLM`, `testCurrent`,
  `isPositive_testCurrent`.
* `testMeasure`, `integral_testMeasure`, `testMeasure_real_univ`, `testMeasure_kahlerTest`,
  `testMeasure_add`, `testMeasure_smul`, `testMeasure_le_smul_traceMeasure`,
  `testMeasure_smulTest`.
* `restrictCurrent`, `restrictCurrent_apply`, `restrictCurrent_apply_of_mem`,
  `isPositive_restrictCurrent`, `mass_restrictCurrent`, `restrictCurrent_add_compl`,
  `restrictCurrent_univ`, `restrictCurrent_eq_zero`, `restrictCurrent_smulTest`,
  `traceMeasure_restrictCurrent`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.CurrentRestriction

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents CurrentTraceMeasure SmoothCurrentTraceMeasure

/-! ### Smooth `0`-forms are functions -/

section ZeroForms

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The function of a smooth `0`-form, read in the preferred chart. -/
def zeroFun (a : SmoothRealForm n M 0) (x : M) : ℝ :=
  a.coeff (complexChartAt x) ((complexChartAt (n := n) x).val x) ![]

/-- A `0`-form has the same value in every chart. -/
theorem zeroFun_symm (a : SmoothRealForm n M 0) {e : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ e.val.target) : zeroFun a (e.val.symm z) = a.coeff e z ![] := by
  set f := complexChartAt (n := n) (e.val.symm z)
  have hx : e.val.symm z ∈ f.val.source := mem_complexChartAt_source _
  have hzs : z ∈ (chartTransition e f).source := by
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
    exact ⟨hz, hx⟩
  rw [a.compatible e f z hzs ![]]
  unfold zeroFun
  congr 1
  exact Subsingleton.elim _ _

theorem chartSmooth_zeroFun (a : SmoothRealForm n M 0) : ChartSmooth (n := n) (zeroFun a) :=
  fun e => ((ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ
    (![] : Fin 0 → ComplexModel n)).contDiff.comp_contDiffOn (a.smooth e)).congr
      fun _ hz => zeroFun_symm a hz

theorem zeroFun_add (a b : SmoothRealForm n M 0) (x : M) :
    zeroFun (a + b) x = zeroFun a x + zeroFun b x := by
  simp [zeroFun, coeff_add]

theorem zeroFun_smul (c : ℝ) (a : SmoothRealForm n M 0) (x : M) :
    zeroFun (c • a) x = c * zeroFun a x := by
  simp [zeroFun, coeff_smul]

theorem zeroFun_smulFun_unitForm (h : M → ℝ) (hh : ChartSmooth (n := n) h) (x : M) :
    zeroFun (smulFun h hh unitForm) x = h x := by
  simp [zeroFun, smulFun_coeff, unitForm_coeff, coordinateWedgeUnit,
    (complexChartAt (n := n) x).val.left_inv (mem_complexChartAt_source x)]

/-- A strongly positive `0`-form is a nonnegative function. -/
theorem zeroFun_nonneg {a : testSpace n M 0} (ha : a ∈ positiveCone n M 0) (x : M) :
    0 ≤ zeroFun (a : SmoothRealForm n M 0) x := by
  have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (ha _ _ hz)
  unfold zeroFun
  have h2 : r • (coordinateWedgeUnit : RealForm n 0) = (r : ℝ) • coordinateWedgeUnit := rfl
  rw [← hr, h2, ContinuousAlternatingMap.smul_apply]
  have h1 : (coordinateWedgeUnit : RealForm n 0) ![] = 1 := by simp [coordinateWedgeUnit]
  rw [h1, smul_eq_mul, mul_one]
  exact r.2

theorem smulTest_congr {q : ℕ} {h h' : M → ℝ} (heq : h = h') (hh : ChartSmooth (n := n) h)
    (hh' : ChartSmooth (n := n) h') (φ : testSpace n M q) : smulTest h hh φ = smulTest h' hh' φ :=
      by
  subst heq
  rfl

theorem smulTest_one {q : ℕ} (φ : testSpace n M q) :
    smulTest (fun _ => 1) (chartSmooth_const 1) φ = φ :=
  Subtype.ext (smoothRealForm_ext fun _ _ => one_smul _ _)

theorem smulTest_add_left {q : ℕ} {h h' : M → ℝ} (hh : ChartSmooth (n := n) h)
    (hh' : ChartSmooth (n := n) h') (φ : testSpace n M q) :
    smulTest (fun x => h x + h' x) ((chartSmoothSubalgebra n M).add_mem
      (show (⟨h, ChartSmooth.continuous hh⟩ : C(M, ℝ)) ∈ chartSmoothSubalgebra n M from hh)
      (show (⟨h', ChartSmooth.continuous hh'⟩ : C(M, ℝ)) ∈ chartSmoothSubalgebra n M from hh')) φ =
      smulTest h hh φ + smulTest h' hh' φ :=
  Subtype.ext (smoothRealForm_ext fun _ _ => add_smul _ _ _)

theorem smulTest_add_right {q : ℕ} {h : M → ℝ} (hh : ChartSmooth (n := n) h)
    (φ ψ : testSpace n M q) : smulTest h hh (φ + ψ) = smulTest h hh φ + smulTest h hh ψ :=
  Subtype.ext (smoothRealForm_ext fun _ _ => smul_add _ _ _)

theorem smulTest_smulTest {q : ℕ} {g h : M → ℝ} (hg : ChartSmooth (n := n) g)
    (hh : ChartSmooth (n := n) h) (φ : testSpace n M q) :
    smulTest g hg (smulTest h hh φ) = smulTest (fun x => g x * h x) (chartSmooth_mul hg hh) φ :=
  Subtype.ext (smoothRealForm_ext fun _ _ => (mul_smul _ _ _).symm)

theorem add_mem_positiveCone {q : ℕ} {φ ψ : testSpace n M q} (hφ : φ ∈ positiveCone n M q)
    (hψ : ψ ∈ positiveCone n M q) : φ + ψ ∈ positiveCone n M q := fun e z hz =>
  (spCone q).add_mem (hφ e z hz) (hψ e z hz)

theorem smul_mem_positiveCone {q : ℕ} {φ : testSpace n M q} (hφ : φ ∈ positiveCone n M q)
    {c : ℝ} (hc : 0 ≤ c) : c • φ ∈ positiveCone n M q := fun e z hz =>
  smul_mem_spCone (hφ e z hz) hc

/-- `a ↦ zeroFun a · ψ`, from test `0`-forms to test forms of bidimension `(q, q)`. -/
def functionTestLM {q : ℕ} (ψ : testSpace n M q) : testSpace n M 0 →ₗ[ℝ] testSpace n M q where
  toFun a := smulTest (zeroFun (a : SmoothRealForm n M 0)) (chartSmooth_zeroFun _) ψ
  map_add' a b := Subtype.ext (smoothRealForm_ext fun e z => by
    simp only [smulTest, Submodule.coe_add, smulFun_coeff, coeff_add]
    rw [zeroFun_add, add_smul])
  map_smul' c a := Subtype.ext (smoothRealForm_ext fun e z => by
    simp only [smulTest, Submodule.coe_smul, smulFun_coeff, coeff_smul, RingHom.id_apply]
    rw [zeroFun_smul, mul_smul])

theorem functionTestLM_smulTest {q : ℕ} (ψ : testSpace n M q) (h : M → ℝ)
    (hh : ChartSmooth (n := n) h) :
    functionTestLM ψ (smulTest h hh (⟨unitForm, unitForm_mem_testSpace⟩ : testSpace n M 0)) =
      smulTest h hh ψ :=
  smulTest_congr (funext fun x => zeroFun_smulFun_unitForm h hh x) _ _ ψ

/-- The current `h ↦ T (h ψ)` of bidimension `(0, 0)`. -/
def testCurrent {q : ℕ} (T : ProductCurrent n M q) (ψ : testSpace n M q) : ProductCurrent n M 0 :=
  T ∘ₗ functionTestLM ψ

theorem isPositive_testCurrent {q : ℕ} {T : ProductCurrent n M q} (hT : IsPositive T)
    {ψ : testSpace n M q} (hψ : ψ ∈ positiveCone n M q) : IsPositive (testCurrent T ψ) :=
  fun _ ha => hT _ (smulTest_mem_positiveCone _ (zeroFun_nonneg ha) hψ)

end ZeroForms

/-! ### The measures `T ∧ ψ` -/

section Measures

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

theorem integrable_of_chartSmooth (μ : Measure M) [IsFiniteMeasure μ] {h : M → ℝ}
    (hh : ChartSmooth (n := n) h) : Integrable h μ :=
  (ChartSmooth.continuous hh).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

/-- **The measure `T ∧ ψ`** of a positive current against a positive test form `ψ`:
`∫ h d(T ∧ ψ) = T (h ψ)` for chart-smooth `h` (`integral_testMeasure`).  It is the trace
measure of the `(0,0)`-current `h ↦ T (h ψ)`. -/
def testMeasure (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) (ψ : testSpace n M q) (hψ : ψ ∈ positiveCone n M q) : Measure M :=
  traceMeasure w (testCurrent T ψ) (isPositive_testCurrent hT hψ)

instance (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) (hT : IsPositive T)
    (ψ : testSpace n M q) (hψ : ψ ∈ positiveCone n M q) :
    IsFiniteMeasure (testMeasure w T hT ψ hψ) := by
  unfold testMeasure
  infer_instance

variable (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) (hT : IsPositive T)

theorem integral_testMeasure (ψ : testSpace n M q) (hψ : ψ ∈ positiveCone n M q) (h : M → ℝ)
    (hh : ChartSmooth (n := n) h) :
    ∫ x, h x ∂(testMeasure w T hT ψ hψ) = T (smulTest h hh ψ) := by
  rw [testMeasure, integral_traceMeasure_chartSmooth _ _ _ h hh]
  exact congrArg T (functionTestLM_smulTest ψ h hh)

theorem testMeasure_congr {ψ ψ' : testSpace n M q} (h : ψ = ψ') (hψ : ψ ∈ positiveCone n M q)
    (hψ' : ψ' ∈ positiveCone n M q) : testMeasure w T hT ψ hψ = testMeasure w T hT ψ' hψ' := by
  subst h
  rfl

theorem testMeasure_real_univ (ψ : testSpace n M q) (hψ : ψ ∈ positiveCone n M q) :
    (testMeasure w T hT ψ hψ).real univ = T ψ := by
  have h := integral_testMeasure w T hT ψ hψ (fun _ => 1) (chartSmooth_const 1)
  rw [smulTest_one] at h
  simpa using h

/-- `T ∧ ω^q` is the trace measure. -/
theorem testMeasure_kahlerTest :
    testMeasure w T hT (kahlerTest w q) (kahlerTest_mem_positiveCone w q) = traceMeasure w T hT :=
  measure_eq_of_integral_chartSmooth_eq (N := n) fun g hg => by
    rw [integral_testMeasure w T hT _ _ g hg, integral_traceMeasure_chartSmooth _ _ _ g hg]

theorem testMeasure_add {ψ ψ' : testSpace n M q} (hψ : ψ ∈ positiveCone n M q)
    (hψ' : ψ' ∈ positiveCone n M q) :
    testMeasure w T hT (ψ + ψ') (add_mem_positiveCone hψ hψ') =
      testMeasure w T hT ψ hψ + testMeasure w T hT ψ' hψ' :=
  measure_eq_of_integral_chartSmooth_eq (N := n) fun g hg => by
    rw [integral_add_measure (integrable_of_chartSmooth _ hg) (integrable_of_chartSmooth _ hg),
      integral_testMeasure w T hT _ _ g hg, integral_testMeasure w T hT _ _ g hg,
      integral_testMeasure w T hT _ _ g hg, smulTest_add_right, map_add]

theorem testMeasure_smul {ψ : testSpace n M q} (hψ : ψ ∈ positiveCone n M q) {c : ℝ}
    (hc : 0 ≤ c) :
    testMeasure w T hT (c • ψ) (smul_mem_positiveCone hψ hc) =
      ENNReal.ofReal c • testMeasure w T hT ψ hψ := by
  have : IsFiniteMeasure (ENNReal.ofReal c • testMeasure w T hT ψ hψ) :=
    ⟨by
      rw [smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  refine measure_eq_of_integral_chartSmooth_eq (N := n) fun g hg => ?_
  rw [integral_smul_measure, integral_testMeasure w T hT _ _ g hg,
    integral_testMeasure w T hT _ _ g hg, ENNReal.toReal_ofReal hc, smul_eq_mul]
  have : smulTest g hg (c • ψ) = c • smulTest g hg ψ :=
    Subtype.ext (smoothRealForm_ext fun _ _ => smul_comm _ _ _)
  rw [this, map_smul, smul_eq_mul]

theorem testMeasure_real_add {ψ ψ' : testSpace n M q} (hψ : ψ ∈ positiveCone n M q)
    (hψ' : ψ' ∈ positiveCone n M q) (E : Set M) :
    (testMeasure w T hT (ψ + ψ') (add_mem_positiveCone hψ hψ')).real E =
      (testMeasure w T hT ψ hψ).real E + (testMeasure w T hT ψ' hψ').real E := by
  rw [testMeasure_add, measureReal_add_apply]

theorem testMeasure_real_smul {ψ : testSpace n M q} (hψ : ψ ∈ positiveCone n M q) {c : ℝ}
    (hc : 0 ≤ c) (E : Set M) :
    (testMeasure w T hT (c • ψ) (smul_mem_positiveCone hψ hc)).real E =
      c * (testMeasure w T hT ψ hψ).real E := by
  rw [testMeasure_smul w T hT hψ hc, measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hc]

/-- **`T ∧ ψ ≤ c σ_T`** when `c ω^q - ψ` is positive. -/
theorem testMeasure_le_smul_traceMeasure {ψ : testSpace n M q} (hψ : ψ ∈ positiveCone n M q)
    {c : ℝ} (hc : 0 ≤ c) (hle : c • kahlerTest w q - ψ ∈ positiveCone n M q) :
    testMeasure w T hT ψ hψ ≤ ENNReal.ofReal c • traceMeasure w T hT := by
  have hω := kahlerTest_mem_positiveCone w q
  have e : ψ + (c • kahlerTest w q - ψ) = c • kahlerTest w q := by abel
  calc testMeasure w T hT ψ hψ
      ≤ testMeasure w T hT ψ hψ + testMeasure w T hT _ hle := Measure.le_add_right le_rfl
    _ = testMeasure w T hT _ (add_mem_positiveCone hψ hle) := (testMeasure_add w T hT hψ hle).symm
    _ = testMeasure w T hT _ (smul_mem_positiveCone hω hc) :=
        testMeasure_congr w T hT e _ _
    _ = ENNReal.ofReal c • traceMeasure w T hT := by
        rw [testMeasure_smul w T hT hω hc, testMeasure_kahlerTest]

/-- `T ∧ (g ψ) = g (T ∧ ψ)` for a chart-smooth `g ≥ 0`. -/
theorem testMeasure_smulTest {ψ : testSpace n M q} (hψ : ψ ∈ positiveCone n M q) {g : M → ℝ}
    (hg : ChartSmooth (n := n) g) (hg0 : ∀ x, 0 ≤ g x) :
    testMeasure w T hT (smulTest g hg ψ) (smulTest_mem_positiveCone hg hg0 hψ) =
      (testMeasure w T hT ψ hψ).withDensity fun x => ENNReal.ofReal (g x) := by
  have hgi : Integrable g (testMeasure w T hT ψ hψ) := integrable_of_chartSmooth _ hg
  have : IsFiniteMeasure ((testMeasure w T hT ψ hψ).withDensity fun x => ENNReal.ofReal (g x)) :=
    isFiniteMeasure_withDensity_ofReal hgi.2
  refine measure_eq_of_integral_chartSmooth_eq (N := n) fun k hk => ?_
  rw [integral_testMeasure w T hT _ _ k hk, smulTest_smulTest,
    integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (g x))
      (ENNReal.measurable_ofReal.comp (ChartSmooth.continuous hg).measurable)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← integral_testMeasure w T hT ψ hψ _ (chartSmooth_mul hk hg)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hg0 x), smul_eq_mul, mul_comm]

end Measures

/-! ### The order-unit constant -/

section Constant

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] (w : KahlerBackground n M) {q : ℕ}

/-- `ω^q` is an order unit: `c ω^q ± φ` is positive for some `c ≥ 0`. -/
theorem exists_const (φ : testSpace n M q) :
    ∃ c : ℝ, 0 ≤ c ∧ c • kahlerTest w q - φ ∈ positiveCone n M q ∧
      c • kahlerTest w q + φ ∈ positiveCone n M q :=
  exists_orderUnit_bound w.isKahler.1 q φ

/-- A constant `c ≥ 0` with `c ω^q ± φ` positive. -/
def restrictConst (φ : testSpace n M q) : ℝ := Classical.choose (exists_const w φ)

theorem restrictConst_nonneg (φ : testSpace n M q) : 0 ≤ restrictConst w φ :=
  (Classical.choose_spec (exists_const w φ)).1

theorem restrictConst_sub (φ : testSpace n M q) :
    restrictConst w φ • kahlerTest w q - φ ∈ positiveCone n M q :=
  (Classical.choose_spec (exists_const w φ)).2.1

theorem restrictConst_add (φ : testSpace n M q) :
    restrictConst w φ • kahlerTest w q + φ ∈ positiveCone n M q :=
  (Classical.choose_spec (exists_const w φ)).2.2

theorem restrictConst_neg (φ : testSpace n M q) :
    restrictConst w φ • kahlerTest w q + -φ ∈ positiveCone n M q := by
  rw [← sub_eq_add_neg]
  exact restrictConst_sub w φ

end Constant

/-! ### The restriction `𝟙_E T` -/

section Restriction

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) (hT : IsPositive T)

/-- The value `(T ∧ (c ω^q + φ))(E) - c σ_T(E)`. -/
def restrictVal (E : Set M) (φ : testSpace n M q) (c : ℝ)
    (hc : c • kahlerTest w q + φ ∈ positiveCone n M q) : ℝ :=
  (testMeasure w T hT _ hc).real E - c * (traceMeasure w T hT).real E

theorem restrictVal_congr (E : Set M) {φ φ' : testSpace n M q} (h : φ = φ') {c : ℝ}
    (hc : c • kahlerTest w q + φ ∈ positiveCone n M q)
    (hc' : c • kahlerTest w q + φ' ∈ positiveCone n M q) :
    restrictVal w T hT E φ c hc = restrictVal w T hT E φ' c hc' := by
  subst h
  rfl

/-- The value does not depend on the constant. -/
theorem restrictVal_eq (E : Set M) (φ : testSpace n M q) {c c' : ℝ} (hc0 : 0 ≤ c)
    (hc'0 : 0 ≤ c') (hc : c • kahlerTest w q + φ ∈ positiveCone n M q)
    (hc' : c' • kahlerTest w q + φ ∈ positiveCone n M q) :
    restrictVal w T hT E φ c hc = restrictVal w T hT E φ c' hc' := by
  have hω := kahlerTest_mem_positiveCone w q
  have e : (c • kahlerTest w q + φ) + c' • kahlerTest w q =
      (c' • kahlerTest w q + φ) + c • kahlerTest w q := by abel
  have h := congrArg (fun μ : Measure M => μ.real E)
    (testMeasure_congr w T hT e (add_mem_positiveCone hc (smul_mem_positiveCone hω hc'0))
      (add_mem_positiveCone hc' (smul_mem_positiveCone hω hc0)))
  rw [testMeasure_real_add w T hT hc (smul_mem_positiveCone hω hc'0),
    testMeasure_real_add w T hT hc' (smul_mem_positiveCone hω hc0),
    testMeasure_real_smul w T hT hω hc'0, testMeasure_real_smul w T hT hω hc0,
    testMeasure_kahlerTest] at h
  unfold restrictVal
  linarith

theorem restrictVal_add (E : Set M) (φ ψ : testSpace n M q) {c d : ℝ}
    (hc : c • kahlerTest w q + φ ∈ positiveCone n M q)
    (hd : d • kahlerTest w q + ψ ∈ positiveCone n M q)
    (hcd : (c + d) • kahlerTest w q + (φ + ψ) ∈ positiveCone n M q) :
    restrictVal w T hT E (φ + ψ) (c + d) hcd =
      restrictVal w T hT E φ c hc + restrictVal w T hT E ψ d hd := by
  have e : (c + d) • kahlerTest w q + (φ + ψ) =
      (c • kahlerTest w q + φ) + (d • kahlerTest w q + ψ) := by
    rw [add_smul]
    abel
  unfold restrictVal
  rw [testMeasure_congr w T hT e hcd (add_mem_positiveCone hc hd),
    testMeasure_real_add w T hT hc hd]
  ring

theorem restrictVal_smul (E : Set M) (φ : testSpace n M q) {c r : ℝ} (hr : 0 ≤ r)
    (hc : c • kahlerTest w q + φ ∈ positiveCone n M q)
    (hrc : (r * c) • kahlerTest w q + r • φ ∈ positiveCone n M q) :
    restrictVal w T hT E (r • φ) (r * c) hrc = r * restrictVal w T hT E φ c hc := by
  have e : (r * c) • kahlerTest w q + r • φ = r • (c • kahlerTest w q + φ) := by
    rw [smul_add, mul_smul]
  unfold restrictVal
  rw [testMeasure_congr w T hT e hrc (smul_mem_positiveCone hc hr), testMeasure_real_smul w T hT
    hc hr]
  ring

theorem restrictVal_neg (E : Set M) (φ : testSpace n M q) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c • kahlerTest w q + φ ∈ positiveCone n M q)
    (hc' : c • kahlerTest w q + -φ ∈ positiveCone n M q) :
    restrictVal w T hT E (-φ) c hc' = -restrictVal w T hT E φ c hc := by
  have hω := kahlerTest_mem_positiveCone w q
  have h2c : (0 : ℝ) ≤ 2 * c := by positivity
  have e : (c • kahlerTest w q + φ) + (c • kahlerTest w q + -φ) = (2 * c) • kahlerTest w q := by
    rw [show (2 : ℝ) * c = c + c by ring, add_smul]
    abel
  have h := congrArg (fun μ : Measure M => μ.real E)
    (testMeasure_congr w T hT e (add_mem_positiveCone hc hc') (smul_mem_positiveCone hω h2c))
  rw [testMeasure_real_add w T hT hc hc', testMeasure_real_smul w T hT hω h2c,
    testMeasure_kahlerTest] at h
  unfold restrictVal
  linarith

/-- The value `𝟙_E T (φ)`. -/
def restrictFun (E : Set M) (φ : testSpace n M q) : ℝ :=
  restrictVal w T hT E φ (restrictConst w φ) (restrictConst_add w φ)

theorem restrictFun_eq (E : Set M) (φ : testSpace n M q) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c • kahlerTest w q + φ ∈ positiveCone n M q) :
    restrictFun w T hT E φ = restrictVal w T hT E φ c hc :=
  restrictVal_eq w T hT E φ (restrictConst_nonneg w φ) hc0 _ hc

theorem restrictFun_add (E : Set M) (φ ψ : testSpace n M q) :
    restrictFun w T hT E (φ + ψ) = restrictFun w T hT E φ + restrictFun w T hT E ψ := by
  have hcd : (restrictConst w φ + restrictConst w ψ) • kahlerTest w q + (φ + ψ) ∈
      positiveCone n M q := by
    have e : (restrictConst w φ + restrictConst w ψ) • kahlerTest w q + (φ + ψ) =
        (restrictConst w φ • kahlerTest w q + φ) + (restrictConst w ψ • kahlerTest w q + ψ) := by
      rw [add_smul]
      abel
    rw [e]
    exact add_mem_positiveCone (restrictConst_add w φ) (restrictConst_add w ψ)
  rw [restrictFun_eq w T hT E (φ + ψ)
      (add_nonneg (restrictConst_nonneg w φ) (restrictConst_nonneg w ψ)) hcd,
    restrictVal_add w T hT E φ ψ (restrictConst_add w φ) (restrictConst_add w ψ) hcd]
  rfl

theorem restrictFun_smul_of_nonneg (E : Set M) (φ : testSpace n M q) {r : ℝ} (hr : 0 ≤ r) :
    restrictFun w T hT E (r • φ) = r * restrictFun w T hT E φ := by
  have hrc : (r * restrictConst w φ) • kahlerTest w q + r • φ ∈ positiveCone n M q := by
    rw [mul_smul, ← smul_add]
    exact smul_mem_positiveCone (restrictConst_add w φ) hr
  rw [restrictFun_eq w T hT E (r • φ) (mul_nonneg hr (restrictConst_nonneg w φ)) hrc,
    restrictVal_smul w T hT E φ hr (restrictConst_add w φ) hrc]
  rfl

theorem restrictFun_neg (E : Set M) (φ : testSpace n M q) :
    restrictFun w T hT E (-φ) = -restrictFun w T hT E φ := by
  rw [restrictFun_eq w T hT E (-φ) (restrictConst_nonneg w φ) (restrictConst_neg w φ),
    restrictVal_neg w T hT E φ (restrictConst_nonneg w φ) (restrictConst_add w φ)
      (restrictConst_neg w φ)]
  rfl

/-- **The restriction `𝟙_E T` of a positive current to a set** (`demailly-cadg:III.1.14`,
`III.2.4`): `𝟙_E T (φ) = (T ∧ φ)(E)`, the signed measure `T ∧ φ` being
`T ∧ (c ω^q + φ) - c σ_T`. -/
def restrictCurrent (E : Set M) : ProductCurrent n M q where
  toFun := restrictFun w T hT E
  map_add' := restrictFun_add w T hT E
  map_smul' r φ := by
    rcases le_or_gt 0 r with hr | hr
    · exact restrictFun_smul_of_nonneg w T hT E φ hr
    · have e : r • φ = (-r) • (-φ) := (neg_smul_neg r φ).symm
      rw [e, restrictFun_smul_of_nonneg w T hT E (-φ) (by linarith), restrictFun_neg]
      simp only [RingHom.id_apply, smul_eq_mul]
      ring

theorem restrictCurrent_apply (E : Set M) (φ : testSpace n M q) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c • kahlerTest w q + φ ∈ positiveCone n M q) :
    restrictCurrent w T hT E φ =
      (testMeasure w T hT _ hc).real E - c * (traceMeasure w T hT).real E :=
  restrictFun_eq w T hT E φ hc0 hc

/-- On a positive test form, `𝟙_E T (φ) = (T ∧ φ)(E)`. -/
theorem restrictCurrent_apply_of_mem (E : Set M) {φ : testSpace n M q}
    (hφ : φ ∈ positiveCone n M q) :
    restrictCurrent w T hT E φ = (testMeasure w T hT φ hφ).real E := by
  have e : (0 : ℝ) • kahlerTest w q + φ = φ := by rw [zero_smul, zero_add]
  have hφ0 : (0 : ℝ) • kahlerTest w q + φ ∈ positiveCone n M q := by rw [e]; exact hφ
  rw [restrictCurrent_apply w T hT E φ le_rfl hφ0, testMeasure_congr w T hT e hφ0 hφ, zero_mul,
    sub_zero]

/-- **`𝟙_E T` is positive.** -/
theorem isPositive_restrictCurrent (E : Set M) : IsPositive (restrictCurrent w T hT E) :=
  fun φ hφ => by
    rw [restrictCurrent_apply_of_mem w T hT E hφ]
    exact measureReal_nonneg

/-- **The mass of `𝟙_E T` is `σ_T(E)`.** -/
theorem mass_restrictCurrent (E : Set M) :
    mass w (restrictCurrent w T hT E) = (traceMeasure w T hT).real E := by
  rw [mass, restrictCurrent_apply_of_mem w T hT E (kahlerTest_mem_positiveCone w q),
    testMeasure_kahlerTest]

/-- **`T = 𝟙_E T + 𝟙_{M \ E} T`** for a measurable set `E`. -/
theorem restrictCurrent_add_compl {E : Set M} (hE : MeasurableSet E) :
    restrictCurrent w T hT E + restrictCurrent w T hT Eᶜ = T := by
  ext φ
  set c := restrictConst w φ
  have hc0 := restrictConst_nonneg w φ
  have hc := restrictConst_add w φ
  rw [LinearMap.add_apply, restrictCurrent_apply w T hT E φ hc0 hc,
    restrictCurrent_apply w T hT Eᶜ φ hc0 hc]
  have h1 := measureReal_add_measureReal_compl (μ := testMeasure w T hT _ hc) hE
  have h2 := measureReal_add_measureReal_compl (μ := traceMeasure w T hT) hE
  rw [testMeasure_real_univ, map_add, map_smul, smul_eq_mul] at h1
  rw [traceMeasure_real_univ] at h2
  have hm : mass w T = T (kahlerTest w q) := rfl
  rw [hm] at h2
  have : c * (traceMeasure w T hT).real E + c * (traceMeasure w T hT).real Eᶜ =
      c * T (kahlerTest w q) := by rw [← mul_add, h2]
  linarith

/-- `𝟙_M T = T`. -/
theorem restrictCurrent_univ : restrictCurrent w T hT univ = T := by
  ext φ
  rw [restrictCurrent_apply w T hT univ φ (restrictConst_nonneg w φ) (restrictConst_add w φ),
    testMeasure_real_univ, traceMeasure_real_univ, map_add, map_smul, smul_eq_mul]
  have hm : mass w T = T (kahlerTest w q) := rfl
  rw [hm]
  ring

/-- **A set of trace measure zero carries no part of `T`**: `σ_T(E) = 0 ⟹ 𝟙_E T = 0`. -/
theorem restrictCurrent_eq_zero {E : Set M} (hE : traceMeasure w T hT E = 0) :
    restrictCurrent w T hT E = 0 := by
  ext φ
  set c := restrictConst w φ
  have hc := restrictConst_add w φ
  obtain ⟨c', hc'0, hc'le, -⟩ := exists_const w (c • kahlerTest w q + φ)
  have hle := testMeasure_le_smul_traceMeasure w T hT hc hc'0 hc'le
  have h0 : testMeasure w T hT _ hc E = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc testMeasure w T hT _ hc E ≤ (ENNReal.ofReal c' • traceMeasure w T hT) E := hle E
      _ = 0 := by rw [smul_apply, hE, smul_zero]
  rw [restrictCurrent_apply w T hT E φ (restrictConst_nonneg w φ) hc, LinearMap.zero_apply,
    measureReal_def, h0, measureReal_def, hE]
  simp

/-- **`𝟙_E T` on function multiples of a positive form**:
`𝟙_E T (h ψ) = ∫_E h d(T ∧ ψ)` for chart-smooth `h` and measurable `E`. -/
theorem restrictCurrent_smulTest {E : Set M} (hE : MeasurableSet E) {ψ : testSpace n M q}
    (hψ : ψ ∈ positiveCone n M q) {h : M → ℝ} (hh : ChartSmooth (n := n) h) :
    restrictCurrent w T hT E (smulTest h hh ψ) = ∫ x in E, h x ∂(testMeasure w T hT ψ hψ) := by
  set C := ‖(⟨h, ChartSmooth.continuous hh⟩ : C(M, ℝ))‖ with hC
  have hbound : ∀ x, |h x| ≤ C := fun x => by
    simpa [Real.norm_eq_abs] using (⟨h, ChartSmooth.continuous hh⟩ : C(M, ℝ)).norm_coe_le_norm x
  have hgs : ChartSmooth (n := n) (fun x => h x + C) := fun e => (hh e).add contDiffOn_const
  have hg0 : ∀ x, 0 ≤ h x + C := fun x => by linarith [neg_abs_le (h x), hbound x]
  have hC0 : 0 ≤ C := norm_nonneg _
  have hsplit : smulTest h hh ψ = smulTest (fun x => h x + C) hgs ψ - C • ψ :=
    Subtype.ext (smoothRealForm_ext fun _ _ => by
      simp only [smulTest, Submodule.coe_sub, Submodule.coe_smul, coeff_sub, coeff_smul,
        smulFun_coeff, add_smul]
      abel)
  have hgψ := smulTest_mem_positiveCone hgs hg0 hψ
  rw [hsplit, map_sub, map_smul, smul_eq_mul, restrictCurrent_apply_of_mem w T hT E hgψ,
    restrictCurrent_apply_of_mem w T hT E hψ, testMeasure_smulTest w T hT hψ hgs hg0,
    measureReal_def, withDensity_apply _ hE,
    ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => hg0 x)
      ((ChartSmooth.continuous hgs).aestronglyMeasurable),
    integral_add (integrable_of_chartSmooth _ hh).integrableOn (integrable_const C),
    setIntegral_const, smul_eq_mul]
  ring

/-- **The trace measure of `𝟙_E T` is `σ_T` restricted to `E`.** -/
theorem traceMeasure_restrictCurrent {E : Set M} (hE : MeasurableSet E) :
    traceMeasure w (restrictCurrent w T hT E) (isPositive_restrictCurrent w T hT E) =
      (traceMeasure w T hT).restrict E :=
  measure_eq_of_integral_chartSmooth_eq (N := n) fun g hg => by
    rw [integral_traceMeasure_chartSmooth _ _ _ g hg,
      restrictCurrent_smulTest w T hT hE (kahlerTest_mem_positiveCone w q) hg,
      testMeasure_kahlerTest]

end Restriction

end SGPT.Foundations.Analysis.Pending.CurrentRestriction
