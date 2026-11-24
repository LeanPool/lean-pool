/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveProductCurrents
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The trace measure of a positive current

Let `T` be a positive current of bidimension `(q,q)` on a compact complex manifold `M`
(`PositiveProductCurrents`) and `ω` a Kähler form.  The functional `h ↦ T (h · ω^q)` on
chart-smooth functions is positive and bounded by `sup |h| · mass T`.  Chart-smooth functions
are dense in `C(M, ℝ)` (Stone--Weierstrass: they form a subalgebra which separates points, by
chart bump functions), so it extends uniquely to a positive continuous functional on `C(M, ℝ)`,
and the Riesz--Markov--Kakutani theorem gives the *trace measure* `σ_T = T ∧ ω^q`
(`demailly-cadg:III.1.14`: a positive current has measure coefficients, and its trace measure
controls them).  It is a finite Borel measure with `∫ h dσ_T = T (h ω^q)` for chart-smooth `h`
and total mass `mass T`.

This is the measure-theoretic side of step B2 of the TN.4 plan: weak limits of currents are
read through their trace measures (masses of compact sets, `bou02-volume:4.12`), and the
restriction `𝟙_Y Θ` of Skoda--El Mir (`demailly-cadg:III.2.3`, step B4) acts through them.

## Main results

* `chartSmoothSubalgebra`, `exists_chartSmooth_bump`, `chartSmoothSubalgebra_separatesPoints`,
  `chartSmoothSubalgebra_topologicalClosure` — chart-smooth functions are uniformly dense in
  `C(M, ℝ)` on a compact manifold.
* `smulFun_mem_testSpace`, `smulFun_mem_positiveCone` — function multiples of test forms.
* `traceExt` — the continuous extension of `h ↦ T (h ω^q)` to `C(M, ℝ)`; `traceExt_nonneg`.
* `traceMeasure` (finite, regular), `integral_traceMeasure`,
  `integral_traceMeasure_chartSmooth`, `traceMeasure_univ`.
* `tendsto_integral_traceMeasure` — weak convergence of positive currents with bounded masses
  gives weak convergence of their trace measures (against all continuous functions);
* `le_traceMeasure_of_tendsto` — masses of closed sets are upper semicontinuous: a lower bound
  `δ ≤ σ_{T_i}(F)` passes to the weak limit (Urysohn + outer regularity), which is the limit
  step of `bou02-volume:4.12` / `dp04-kahler-cone:2.6`.
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff ENNReal CompactlySupported

namespace SGPT.Foundations.Analysis.Pending.CurrentTraceMeasure

open FirstPass FirstPass.PositiveClasses StronglyPositiveForms ProductTestForms
  OrderUnitWeakCompactness PositiveProductCurrents

noncomputable section

/-! ### Chart-smooth functions are dense -/

section Dense

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable (n M) in
/-- The chart-smooth continuous functions, a subalgebra of `C(M, ℝ)`. -/
def chartSmoothSubalgebra : Subalgebra ℝ C(M, ℝ) where
  carrier := {g | ChartSmooth (n := n) ⇑g}
  mul_mem' := fun {a b} ha hb e => (ha e).mul (hb e)
  add_mem' := fun {a b} ha hb e => (ha e).add (hb e)
  algebraMap_mem' := fun c e => by
    change ContDiffOn ℝ ∞ (fun _ => c) e.val.target
    exact contDiffOn_const

omit [IsComplexManifold n M] in
theorem mem_chartSmoothSubalgebra {g : C(M, ℝ)} :
    g ∈ chartSmoothSubalgebra n M ↔ ChartSmooth (n := n) ⇑g := Iff.rfl

/-- **Chart bump functions.**  Every neighbourhood `V` of a point `x` carries a chart-smooth
function with values in `[0,1]`, equal to `1` at `x` and vanishing off `V`. -/
theorem exists_chartSmooth_bump (x : M) {V : Set M} (hV : V ∈ 𝓝 x) :
    ∃ h : M → ℝ, ChartSmooth (n := n) h ∧ h x = 1 ∧ (∀ y, y ∉ V → h y = 0) ∧
      ∀ y, 0 ≤ h y ∧ h y ≤ 1 := by
  classical
  set e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hex : e.val x ∈ e.val.target := e.val.map_source hx
  -- a closed ball around `e x` inside the target whose inverse image lies in `V`
  have hW : e.val.target ∩ e.val.symm ⁻¹' (V ∩ e.val.source) ∈ 𝓝 (e.val x) := by
    refine inter_mem (e.val.open_target.mem_nhds hex) ?_
    have hc := e.val.continuousAt_symm hex
    have hs : V ∩ e.val.source ∈ 𝓝 (e.val.symm (e.val x)) := by
      rw [e.val.left_inv hx]
      exact inter_mem hV (e.val.open_source.mem_nhds hx)
    exact hc hs
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
  have hclosed : closedBall (e.val x) (r / 2) ⊆ e.val.target ∩ e.val.symm ⁻¹' (V ∩ e.val.source) :=
    (closedBall_subset_ball (by linarith)).trans hball
  let χ : ContDiffBump (e.val x) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let h : M → ℝ := fun y => if y ∈ e.val.source then χ (e.val y) else 0
  -- the compact set carrying the bump, read on `M`
  set K : Set M := e.val.symm '' closedBall (e.val x) (r / 2)
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.val.continuousOn_symm.mono fun z hz => (hclosed hz).1)
  have hKsrc : K ⊆ e.val.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact ((hclosed hz).2).2
  have hzero : ∀ y, y ∉ K → h y = 0 := by
    intro y hy
    by_cases hys : y ∈ e.val.source
    · simp only [h, hys, ite_true]
      refine χ.zero_of_le_dist ?_
      by_contra hlt
      push Not at hlt
      exact hy ⟨e.val y, mem_closedBall.mpr hlt.le, e.val.left_inv hys⟩
    · simp only [h, hys, ite_false]
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · -- chart-smoothness
    intro d w hw
    by_cases hws : d.val.symm w ∈ e.val.source
    · have hO : (chartTransition d e).source ∈ 𝓝 w :=
        (chartTransition d e).open_source.mem_nhds ⟨hw, hws⟩
      have hT : ContDiffAt ℝ ∞ (chartTransition d e) w :=
        HolomorphicMaps.chartTransition_contDiffAt_real d e ⟨hw, hws⟩
      have hcomp : ContDiffAt ℝ ∞ (fun w' => χ (chartTransition d e w')) w :=
        χ.contDiff.contDiffAt.comp w hT
      refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [hO] with w' hw'
      have : d.val.symm w' ∈ e.val.source := hw'.2
      simp only [h, this, ite_true]
      rfl
    · have hKcl : IsClosed K := hKc.isClosed
      have hO : d.val.target ∩ d.val.symm ⁻¹' Kᶜ ∈ 𝓝 w :=
        (d.val.continuousOn_symm.isOpen_inter_preimage d.val.open_target
          hKcl.isOpen_compl).mem_nhds ⟨hw, fun hK => hws (hKsrc hK)⟩
      refine (contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [hO] with w' hw'
      exact hzero _ hw'.2
  · simp only [h, hx, ite_true]
    exact χ.one_of_mem_closedBall (mem_closedBall_self (by positivity))
  · intro y hyV
    refine hzero y ?_
    rintro ⟨z, hz, rfl⟩
    exact hyV ((hclosed hz).2).1
  · intro y
    by_cases hys : y ∈ e.val.source
    · simp only [h, hys, ite_true]
      exact ⟨χ.nonneg, χ.le_one⟩
    · simp only [h, hys, ite_false]
      exact ⟨le_rfl, zero_le_one⟩

omit [IsComplexManifold n M] in
/-- A chart-smooth function is continuous. -/
theorem chartSmooth_continuous {h : M → ℝ} (hh : ChartSmooth (n := n) h) : Continuous h :=
  ProductTestForms.ChartSmooth.continuous hh

theorem chartSmoothSubalgebra_separatesPoints :
    (chartSmoothSubalgebra n M).SeparatesPoints := by
  intro x y hxy
  obtain ⟨h, hh, hx, hy, -⟩ := exists_chartSmooth_bump (n := n) x
    (isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.mpr hxy) : ({y}ᶜ : Set M) ∈ 𝓝 x)
  refine ⟨h, ⟨⟨h, chartSmooth_continuous hh⟩, hh, rfl⟩, ?_⟩
  rw [hx, hy y (by simp)]
  exact one_ne_zero

/-- **Chart-smooth functions are uniformly dense** in `C(M, ℝ)` (Stone--Weierstrass). -/
theorem chartSmoothSubalgebra_topologicalClosure [CompactSpace M] :
    (chartSmoothSubalgebra n M).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    chartSmoothSubalgebra_separatesPoints

end Dense

/-! ### Function multiples of test forms -/

section Multiples

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
theorem chartSmooth_mul {g h : M → ℝ} (hg : ChartSmooth (n := n) g)
    (hh : ChartSmooth (n := n) h) : ChartSmooth (n := n) (fun x => g x * h x) :=
  fun e => (hg e).mul (hh e)

theorem smulFun_add {k : ℕ} (h : M → ℝ) (hh : ChartSmooth (n := n) h)
    (a b : SmoothRealForm n M k) : smulFun h hh (a + b) = smulFun h hh a + smulFun h hh b :=
  smoothRealForm_ext fun _ _ => smul_add _ _ _

theorem smulFun_smul {k : ℕ} (h : M → ℝ) (hh : ChartSmooth (n := n) h) (c : ℝ)
    (a : SmoothRealForm n M k) : smulFun h hh (c • a) = c • smulFun h hh a :=
  smoothRealForm_ext fun _ _ => smul_comm _ _ _

theorem smulFun_zero {k : ℕ} (h : M → ℝ) (hh : ChartSmooth (n := n) h) :
    smulFun h hh (0 : SmoothRealForm n M k) = 0 :=
  smoothRealForm_ext fun _ _ => smul_zero _

theorem smulFun_wedgeTwo {k : ℕ} (h : M → ℝ) (hh : ChartSmooth (n := n) h)
    (P : SmoothRealForm n M k) (β : SmoothRealForm n M 2) :
    smulFun h hh (wedgeTwo P β) = wedgeTwo (smulFun h hh P) β :=
  smoothRealForm_ext fun _ _ => (coordinateWedge_smul_left _ _ _).symm

/-- Function multiples of test forms are test forms. -/
theorem smulFun_mem_testSpace (h : M → ℝ) (hh : ChartSmooth (n := n) h) :
    ∀ (q : ℕ) {φ : SmoothRealForm n M (2 * q)}, φ ∈ testSpace n M q →
      smulFun h hh φ ∈ testSpace n M q
  | 0, φ, hφ => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      have : smulFun h hh (smulFun g hg unitForm) =
          smulFun (fun x => h x * g x) (chartSmooth_mul hh hg) unitForm :=
        smoothRealForm_ext fun _ _ => (mul_smul _ _ _).symm
      rw [this]
      exact smulFun_unitForm_mem_testSpace _ _
    | zero => rw [smulFun_zero]; exact (testSpace n M 0).zero_mem
    | add x y _ _ hx hy => rw [smulFun_add]; exact (testSpace n M 0).add_mem hx hy
    | smul a x _ hx => rw [smulFun_smul]; exact (testSpace n M 0).smul_mem a hx
  | q + 1, φ, hφ => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, hP, β, hβ, rfl⟩ := hx
      rw [smulFun_wedgeTwo]
      exact wedgeTwo_mem_testSpace (smulFun_mem_testSpace h hh q hP) hβ
    | zero => rw [smulFun_zero]; exact (testSpace n M (q + 1)).zero_mem
    | add x y _ _ hx hy => rw [smulFun_add]; exact (testSpace n M (q + 1)).add_mem hx hy
    | smul a x _ hx => rw [smulFun_smul]; exact (testSpace n M (q + 1)).smul_mem a hx

/-- A function multiple of a test form, as a test form. -/
def smulTest {q : ℕ} (h : M → ℝ) (hh : ChartSmooth (n := n) h) (φ : testSpace n M q) :
    testSpace n M q :=
  ⟨smulFun h hh φ, smulFun_mem_testSpace h hh q φ.2⟩

/-- A nonnegative multiple of a positive test form is positive. -/
theorem smulTest_mem_positiveCone {q : ℕ} {h : M → ℝ} (hh : ChartSmooth (n := n) h)
    (hpos : ∀ x, 0 ≤ h x) {φ : testSpace n M q} (hφ : φ ∈ positiveCone n M q) :
    smulTest h hh φ ∈ positiveCone n M q := fun e z hz =>
  smul_mem_spCone (hφ e z hz) (hpos _)

end Multiples

/-! ### The trace functional and its extension -/

section Trace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The chart-smooth functions as a normed subspace of `C(M, ℝ)`. -/
abbrev smoothSubspace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] : Submodule ℝ C(M, ℝ) :=
  Subalgebra.toSubmodule (chartSmoothSubalgebra n M)

/-- The trace functional `h ↦ T (h ω^q)` on chart-smooth functions. -/
def traceLM (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) :
    smoothSubspace n M →ₗ[ℝ] ℝ where
  toFun g := T (smulTest (⇑(g : C(M, ℝ))) g.2 (kahlerTest w q))
  map_add' g g' := by
    have h : smulTest (⇑((g + g' : smoothSubspace n M) : C(M, ℝ))) (g + g').2 (kahlerTest w q) =
        smulTest (⇑(g : C(M, ℝ))) g.2 (kahlerTest w q) +
          smulTest (⇑(g' : C(M, ℝ))) g'.2 (kahlerTest w q) :=
      Subtype.ext (smoothRealForm_ext fun _ _ => add_smul _ _ _)
    rw [h, map_add]
  map_smul' c g := by
    have h : smulTest (⇑((c • g : smoothSubspace n M) : C(M, ℝ))) (c • g).2 (kahlerTest w q) =
        c • smulTest (⇑(g : C(M, ℝ))) g.2 (kahlerTest w q) :=
      Subtype.ext (smoothRealForm_ext fun _ _ => mul_smul _ _ _)
    rw [h, map_smul]
    rfl

theorem traceLM_apply (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (g : smoothSubspace n M) :
    traceLM w T g = T (smulTest (⇑(g : C(M, ℝ))) g.2 (kahlerTest w q)) := rfl

/-- The trace functional is monotone under pointwise comparison of functions. -/
theorem traceLM_nonneg (w : KahlerBackground n M) {q : ℕ} {T : ProductCurrent n M q}
    (hT : IsPositive T) {g : smoothSubspace n M} (hg : ∀ x, 0 ≤ (g : C(M, ℝ)) x) :
    0 ≤ traceLM w T g :=
  hT _ (smulTest_mem_positiveCone g.2 hg (kahlerTest_mem_positiveCone w q))

omit [IsComplexManifold n M] in
theorem constant_mem_smoothSubspace (c : ℝ) :
    (ContinuousMap.const M c) ∈ smoothSubspace n M :=
  fun _ => contDiffOn_const

theorem traceLM_const (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) (c : ℝ) :
    traceLM w T ⟨ContinuousMap.const M c, constant_mem_smoothSubspace c⟩ = c * mass w T := by
  have h : smulTest (⇑(ContinuousMap.const M c)) (constant_mem_smoothSubspace c)
      (kahlerTest w q) = c • kahlerTest w q :=
    Subtype.ext (smoothRealForm_ext fun _ _ => rfl)
  rw [traceLM_apply]
  erw [h]
  rw [map_smul, smul_eq_mul]
  rfl

variable [CompactSpace M]

/-- **The trace functional is bounded by the mass**: `|T (h ω^q)| ≤ sup |h| · mass T`. -/
theorem abs_traceLM_le (w : KahlerBackground n M) {q : ℕ} {T : ProductCurrent n M q}
    (hT : IsPositive T) (g : smoothSubspace n M) :
    |traceLM w T g| ≤ ‖g‖ * mass w T := by
  set c := ‖(g : C(M, ℝ))‖
  have hle : ∀ x, |(g : C(M, ℝ)) x| ≤ c := fun x => by
    simpa [Real.norm_eq_abs] using (g : C(M, ℝ)).norm_coe_le_norm x
  let G : smoothSubspace n M := ⟨ContinuousMap.const M c, constant_mem_smoothSubspace c⟩
  have h₁ := traceLM_nonneg w hT (g := G - g) fun x => by
    have := hle x
    simp only [Submodule.coe_sub, ContinuousMap.sub_apply, ContinuousMap.const_apply, G]
    linarith [le_abs_self ((g : C(M, ℝ)) x)]
  have h₂ := traceLM_nonneg w hT (g := G + g) fun x => by
    have := hle x
    simp only [Submodule.coe_add, ContinuousMap.add_apply, ContinuousMap.const_apply, G]
    linarith [neg_abs_le ((g : C(M, ℝ)) x)]
  rw [map_sub, traceLM_const] at h₁
  rw [map_add, traceLM_const] at h₂
  rw [abs_le]
  have hnorm : ‖g‖ = c := rfl
  rw [hnorm]
  constructor <;> linarith

/-- The trace functional as a continuous linear map on the chart-smooth functions. -/
def traceCLM (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) : smoothSubspace n M →L[ℝ] ℝ :=
  (traceLM w T).mkContinuous (mass w T) fun g => by
    rw [Real.norm_eq_abs, mul_comm]
    exact abs_traceLM_le w hT g

theorem denseRange_smoothSubspace_subtypeL :
    DenseRange ((smoothSubspace n M).subtypeL : smoothSubspace n M →L[ℝ] C(M, ℝ)) := by
  rw [DenseRange, Submodule.coe_subtypeL, Submodule.coe_subtype, Subtype.range_coe_subtype]
  have h := congrArg (fun A : Subalgebra ℝ C(M, ℝ) => (A : Set C(M, ℝ)))
    (chartSmoothSubalgebra_topologicalClosure (n := n) (M := M))
  simp only [Subalgebra.topologicalClosure_coe, Algebra.coe_top] at h
  exact dense_iff_closure_eq.mpr h

omit [CompactSpace M] in
omit [IsComplexManifold n M] in
theorem isUniformInducing_smoothSubspace_subtypeL :
    IsUniformInducing ((smoothSubspace n M).subtypeL : smoothSubspace n M →L[ℝ] C(M, ℝ)) :=
  isUniformEmbedding_subtype_val.isUniformInducing

/-- **The trace functional on all continuous functions**: the unique continuous extension of
`h ↦ T (h ω^q)` from chart-smooth `h` to `C(M, ℝ)`. -/
def traceExt (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) : C(M, ℝ) →L[ℝ] ℝ :=
  (traceCLM w T hT).extend (smoothSubspace n M).subtypeL

theorem traceExt_smooth (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) (g : smoothSubspace n M) :
    traceExt w T hT (g : C(M, ℝ)) = traceLM w T g :=
  ContinuousLinearMap.extend_eq (traceCLM w T hT) denseRange_smoothSubspace_subtypeL
    isUniformInducing_smoothSubspace_subtypeL g

/-- The extension is positive. -/
theorem traceExt_nonneg (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) {f : C(M, ℝ)} (hf : ∀ x, 0 ≤ f x) : 0 ≤ traceExt w T hT f := by
  by_contra hneg
  push Not at hneg
  set L := traceExt w T hT
  set a := -L f with ha
  have hapos : 0 < a := by linarith
  set ε := a / (2 * (‖L‖ + 1)) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (chartSmoothSubalgebra n M) chartSmoothSubalgebra_separatesPoints f ε hεpos
  -- `g + ε` is a nonnegative chart-smooth function within `2ε` of `f`
  let G : smoothSubspace n M :=
    ⟨(g : C(M, ℝ)) + ContinuousMap.const M ε,
      (smoothSubspace n M).add_mem g.2 (constant_mem_smoothSubspace ε)⟩
  have hGnn : ∀ x, 0 ≤ (G : C(M, ℝ)) x := fun x => by
    have hx : |(g : C(M, ℝ)) x - f x| ≤ ‖(g : C(M, ℝ)) - f‖ := by
      simpa [Real.norm_eq_abs] using ((g : C(M, ℝ)) - f).norm_coe_le_norm x
    have := hf x
    simp only [G, ContinuousMap.add_apply, ContinuousMap.const_apply]
    linarith [neg_abs_le ((g : C(M, ℝ)) x - f x)]
  have hLG : 0 ≤ L (G : C(M, ℝ)) := by
    rw [traceExt_smooth]
    exact traceLM_nonneg w hT hGnn
  have hdist : ‖(G : C(M, ℝ)) - f‖ ≤ 2 * ε := by
    have h1 : (G : C(M, ℝ)) - f = ((g : C(M, ℝ)) - f) + ContinuousMap.const M ε := by
      simp only [G]; abel
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖ContinuousMap.const M ε‖ ≤ ε := by
      refine (ContinuousMap.norm_le _ hεpos.le).mpr fun _ => ?_
      simp [abs_of_pos hεpos]
    linarith
  have hLdiff : |L (G : C(M, ℝ)) - L f| ≤ ‖L‖ * (2 * ε) := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
  have hkey : ‖L‖ * (2 * ε) < a := by
    rw [hε]
    have hpos : 0 < ‖L‖ + 1 := by positivity
    rw [show ‖L‖ * (2 * (a / (2 * (‖L‖ + 1)))) = a * (‖L‖ / (‖L‖ + 1)) by field_simp]
    have : ‖L‖ / (‖L‖ + 1) < 1 := (div_lt_one hpos).mpr (by linarith)
    nlinarith
  have := le_abs_self (L (G : C(M, ℝ)) - L f)
  linarith

end Trace

/-! ### The trace measure -/

section Measure

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Compactly supported continuous functions are continuous functions (linearly). -/
def ccToContinuous : C_c(M, ℝ) →ₗ[ℝ] C(M, ℝ) where
  toFun f := f.toContinuousMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- On a compact manifold every continuous function is compactly supported. -/
def continuousToCc (f : C(M, ℝ)) : C_c(M, ℝ) :=
  ⟨f, isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)⟩

/-- The positive functional `f ↦ (T ∧ ω^q)(f)` on compactly supported functions. -/
def tracePositiveMap (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) : C_c(M, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((traceExt w T hT).toLinearMap ∘ₗ ccToContinuous)
    fun _ hf => traceExt_nonneg w T hT fun x => hf x

/-- **The trace measure** `σ_T = T ∧ ω^q` of a positive current (Riesz--Markov--Kakutani). -/
def traceMeasure (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) : Measure M :=
  RealRMK.rieszMeasure (tracePositiveMap w T hT)

instance (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) (hT : IsPositive T) :
    (traceMeasure w T hT).Regular :=
  RealRMK.regular_rieszMeasure _

instance (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q) (hT : IsPositive T) :
    IsFiniteMeasure (traceMeasure w T hT) :=
  inferInstance

/-- Integrals of continuous functions against the trace measure. -/
theorem integral_traceMeasure (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) (f : C(M, ℝ)) :
    ∫ x, f x ∂(traceMeasure w T hT) = traceExt w T hT f :=
  RealRMK.integral_rieszMeasure (tracePositiveMap w T hT) (continuousToCc f)

/-- **The trace measure computes the current on function multiples of `ω^q`**:
`∫ h dσ_T = T (h ω^q)` for chart-smooth `h`. -/
theorem integral_traceMeasure_chartSmooth (w : KahlerBackground n M) {q : ℕ}
    (T : ProductCurrent n M q) (hT : IsPositive T) (h : M → ℝ) (hh : ChartSmooth (n := n) h) :
    ∫ x, h x ∂(traceMeasure w T hT) = T (smulTest h hh (kahlerTest w q)) := by
  have := integral_traceMeasure w T hT ⟨h, chartSmooth_continuous hh⟩
  rw [show traceExt w T hT ⟨h, chartSmooth_continuous hh⟩ =
      traceExt w T hT ((⟨⟨h, chartSmooth_continuous hh⟩, hh⟩ : smoothSubspace n M) :
        C(M, ℝ)) from rfl, traceExt_smooth] at this
  exact this

/-- The total mass of the trace measure is the mass of the current. -/
theorem traceMeasure_real_univ (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) : (traceMeasure w T hT).real univ = mass w T := by
  have h := integral_traceMeasure w T hT (ContinuousMap.const M 1)
  rw [show traceExt w T hT (ContinuousMap.const M 1) =
      traceExt w T hT ((⟨ContinuousMap.const M 1, constant_mem_smoothSubspace 1⟩ :
        smoothSubspace n M) : C(M, ℝ)) from rfl, traceExt_smooth, traceLM_const, one_mul] at h
  simpa using h

theorem traceMeasure_univ (w : KahlerBackground n M) {q : ℕ} (T : ProductCurrent n M q)
    (hT : IsPositive T) : traceMeasure w T hT univ = ENNReal.ofReal (mass w T) := by
  rw [← traceMeasure_real_univ w T hT, measureReal_def, ENNReal.ofReal_toReal
    (measure_ne_top _ _)]

end Measure

/-! ### Weak convergence of currents and of their trace measures -/

section Convergence

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

theorem abs_integral_traceMeasure_sub_le (w : KahlerBackground n M) {q : ℕ}
    (T : ProductCurrent n M q) (hT : IsPositive T) (f g : C(M, ℝ)) :
    |∫ x, f x ∂(traceMeasure w T hT) - ∫ x, g x ∂(traceMeasure w T hT)| ≤
      ‖f - g‖ * mass w T := by
  rw [← integral_sub (f.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)))
    (g.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))),
    ← traceMeasure_real_univ w T hT, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
  simpa using (f - g).norm_coe_le_norm x

/-- **Weak convergence of currents gives weak convergence of trace measures.**  If positive
currents `T_i` converge weakly to `S` along a filter with eventually bounded masses, then
`∫ f dσ_{T_i} → ∫ f dσ_S` for every continuous `f`. -/
theorem tendsto_integral_traceMeasure (w : KahlerBackground n M) {q : ℕ} {ι : Type*}
    {l : Filter ι} {T : ι → ProductCurrent n M q} (hT : ∀ i, IsPositive (T i))
    {S : ProductCurrent n M q} (hS : IsPositive S) {m : ℝ}
    (hm : ∀ᶠ i in l, mass w (T i) ≤ m) (hlim : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (S φ)))
    (f : C(M, ℝ)) :
    Tendsto (fun i => ∫ x, f x ∂(traceMeasure w (T i) (hT i))) l
      (𝓝 (∫ x, f x ∂(traceMeasure w S hS))) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hmS : mass w S ≤ m := le_of_tendsto (tendsto_mass hlim) hm
  have hm0 : 0 ≤ m := (mass_nonneg w hS).trans hmS
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (3 * (m + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (chartSmoothSubalgebra n M) chartSmoothSubalgebra_separatesPoints f δ hδpos
  have hgs : ChartSmooth (n := n) ⇑(g : C(M, ℝ)) := g.2
  -- the smooth part converges
  have hsmooth := hlim (smulTest (⇑(g : C(M, ℝ))) hgs (kahlerTest w q))
  rw [Metric.tendsto_nhds] at hsmooth
  have hfg : ‖f - (g : C(M, ℝ))‖ < δ := by rw [norm_sub_rev]; exact hg
  have hmδ : m * δ < ε / 3 := by
    rw [hδ]
    have : 0 < m + 1 := by linarith
    rw [show m * (ε / (3 * (m + 1))) = ε / 3 * (m / (m + 1)) by field_simp]
    have : m / (m + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    nlinarith
  filter_upwards [hm, hsmooth (ε / 3) (by positivity)] with i hmi hi
  rw [Real.dist_eq] at hi ⊢
  rw [← integral_traceMeasure_chartSmooth w (T i) (hT i) _ hgs,
    ← integral_traceMeasure_chartSmooth w S hS _ hgs] at hi
  have h₁ := abs_integral_traceMeasure_sub_le w (T i) (hT i) f g
  have h₂ := abs_integral_traceMeasure_sub_le w S hS f g
  have hmi0 : 0 ≤ mass w (T i) := mass_nonneg w (hT i)
  have e₁ : ‖f - (g : C(M, ℝ))‖ * mass w (T i) ≤ m * δ := by
    rw [mul_comm]; exact mul_le_mul hmi hfg.le (norm_nonneg _) hm0
  have e₂ : ‖f - (g : C(M, ℝ))‖ * mass w S ≤ m * δ := by
    rw [mul_comm]; exact mul_le_mul hmS hfg.le (norm_nonneg _) hm0
  have t₁ := abs_sub_le (∫ x, f x ∂(traceMeasure w (T i) (hT i)))
    (∫ x, (g : C(M, ℝ)) x ∂(traceMeasure w (T i) (hT i))) (∫ x, f x ∂(traceMeasure w S hS))
  have t₂ := abs_sub_le (∫ x, (g : C(M, ℝ)) x ∂(traceMeasure w (T i) (hT i)))
    (∫ x, (g : C(M, ℝ)) x ∂(traceMeasure w S hS)) (∫ x, f x ∂(traceMeasure w S hS))
  rw [abs_sub_comm (∫ x, (g : C(M, ℝ)) x ∂(traceMeasure w S hS))] at t₂
  linarith

/-- **Masses of closed sets are upper semicontinuous under weak convergence**
(`bou02-volume:4.12`, last step): if positive currents `T_i` converge weakly to `S` with
eventually bounded masses and their trace measures eventually give mass `≥ δ` to a closed set
`F`, so does the trace measure of `S`. -/
theorem le_traceMeasure_of_tendsto (w : KahlerBackground n M) {q : ℕ} {ι : Type*}
    {l : Filter ι} [l.NeBot] {T : ι → ProductCurrent n M q} (hT : ∀ i, IsPositive (T i))
    {S : ProductCurrent n M q} (hS : IsPositive S) {m : ℝ}
    (hm : ∀ᶠ i in l, mass w (T i) ≤ m) (hlim : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (S φ)))
    {F : Set M} (hF : IsClosed F) {δ : ℝ}
    (hδ : ∀ᶠ i in l, δ ≤ (traceMeasure w (T i) (hT i)).real F) :
    δ ≤ (traceMeasure w S hS).real F := by
  by_contra hlt
  push Not at hlt
  have hlt' : traceMeasure w S hS F < ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (traceMeasure w S hS) F)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr hlt
  obtain ⟨U, hFU, hU, hUlt⟩ := Set.exists_isOpen_lt_of_lt F (ENNReal.ofReal δ) hlt'
  have hUlt' : (traceMeasure w S hS).real U < δ := by
    have hδ0 : 0 < δ := by
      by_contra h0
      push Not at h0
      exact absurd hUlt (by rw [ENNReal.ofReal_of_nonpos h0]; exact not_lt_zero)
    rw [measureReal_def]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hUlt
      |>.trans_le
      (ENNReal.toReal_ofReal hδ0.le).le
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl hF
    (disjoint_compl_left_iff_subset.mpr hFU)
  have hfint : ∀ μ : Measure M, IsFiniteMeasure μ → Integrable (fun x => f x) μ := fun μ _ =>
    f.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  -- `𝟙_F ≤ f ≤ 𝟙_U`
  have hlow : ∀ μ : Measure M, IsFiniteMeasure μ → μ.real F ≤ ∫ x, f x ∂μ := fun μ _ => by
    rw [← integral_indicator_one hF.measurableSet]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hF.measurableSet)
      (hfint μ inferInstance) fun x => ?_
    by_cases hx : x ∈ F
    · simp [hx, hf1 hx]
    · simp only [indicator_of_notMem hx]
      exact (hf01 x).1
  have hup : ∀ μ : Measure M, IsFiniteMeasure μ → ∫ x, f x ∂μ ≤ μ.real U := fun μ _ => by
    rw [← integral_indicator_one hU.measurableSet]
    refine integral_mono (hfint μ inferInstance)
      ((integrable_const (1 : ℝ)).indicator hU.measurableSet) fun x => ?_
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx, Pi.one_apply]
      exact (hf01 x).2
    · have : f x = 0 := hf0 hx
      simp [hx, this]
  have hconv := tendsto_integral_traceMeasure w hT hS hm hlim f
  have hge : δ ≤ ∫ x, f x ∂(traceMeasure w S hS) :=
    ge_of_tendsto hconv (hδ.mono fun i hi => hi.trans (hlow _ inferInstance))
  have := hup (traceMeasure w S hS) inferInstance
  linarith

end Convergence

end

end SGPT.Foundations.Analysis.Pending.CurrentTraceMeasure
