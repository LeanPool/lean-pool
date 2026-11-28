/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense
public import Mathlib.Algebra.Ring.IsFormallyReal

/-! # Simple processes are dense in the bracket-weighted predictable `L²`

`ItoIntegralCLM.simpleAssemblyHorizon_denseRange` puts the simple processes densely inside
`L²(trim_T)`. The Itô integral against `M = φ●B` lives on the **weighted** space
`L²(φ²·trim_T)` instead — `φ²ds` being the bracket `d⟨M⟩` — and its characterisation as *the*
stochastic integral, as well as the passage from simple strategies to general ones, both need
density there.

## The argument, and why it is short

The flat density proof is a π-λ induction over the predictable rectangles, and porting it
wholesale to a second measure would duplicate its longest argument. It does not need porting.
Its core, `ItoIntegralCLM.setIntegral_eq_zero_of_orthogonal_pred`, is a statement about an
*integrable* function on `trim_T`, and the weighted problem reduces to it by moving the weight
into the integrand: if `g ∈ L²(f²·trim_T)` is orthogonal to every simple process, then

  `h := f²·g`

is `trim_T`-integrable (`∫|h| d(trim) = ∫|g| d(f²·trim) ≤ ‖g‖·(f²·trim)(univ)^{1/2}`), and
orthogonality says exactly that `∫_R h d(trim) = 0` on every predictable rectangle `R`. The
π-λ core then gives `h = 0` a.e., and since `f²·trim_T` is carried by `{f ≠ 0}`, that is
`g = 0` a.e. for the weighted measure.

So the weight is handled where it is cheap — inside the integrand — and the hard measure
theory is used once, unchanged. `setIntegral_eq_zero_of_orthogonal_pred` was weakened from an
`L²` class to an integrable function for exactly this call; `h` is `L¹` and generally not `L²`.

## Main definitions

* `simpleAssemblyOfMeasure`: the embedding of the bounded simple processes into `L²(ν)` for an
  arbitrary finite measure `ν` on the predictable σ-algebra, the analogue of `simpleAssemblyHorizon`
  with the trim measure replaced by `ν`.

## Main results

* `memLp_uncurry_of_isFiniteMeasure` — a simple process is `L²` for *any* finite predictable
  measure, since `SimpleProcess.coe_bounded` bounds it uniformly.
* `isFiniteMeasure_sqWeight` — `f²·trim_T` is finite exactly because `f ∈ L²(trim_T)`.
* `inner_simpleAssemblyOfMeasure_iocSPHorizon` — the rectangle inner product, where the weight moves
  from the measure into the integrand.
* `simpleAssembly_sqWeight_denseRange` — the density theorem.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  3.2.5

## Tags

density of simple processes, weighted predictable L2, bracket-weighted space,
stochastic integral construction, predictable rectangles, MSC 60H05, MSC 60G07
-/

@[expose] public section

namespace MathFin
namespace PredictableDensityGeneral

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM LpMulIsometry
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### A simple process is `L²` for every finite predictable measure -/

/-- A simple process is bounded (`SimpleProcess.coe_bounded`), so it is square-integrable
against **any** finite measure on the predictable σ-algebra — no relation to `trim_T` needed.
This is what lets the same `TBoundedSP` index the weighted space. -/
lemma memLp_uncurry_of_isFiniteMeasure (hBmeas : ∀ t, Measurable (B t))
    (ν : @Measure (ℝ≥0 × Ω)
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable) [IsFiniteMeasure ν]
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (Function.uncurry ⇑V) 2 ν := by
  obtain ⟨C, hC⟩ := V.coe_bounded
  exact MemLp.of_bound V.isStronglyPredictable.aestronglyMeasurable C
    (Eventually.of_forall fun z ↦ hC z.1 z.2)

/-- **The weighted simple-process embedding**, the analogue of `simpleAssemblyHorizon` with the
trim measure replaced by an arbitrary finite predictable `ν`. -/
noncomputable def simpleAssemblyOfMeasure (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (ν : @Measure (ℝ≥0 × Ω)
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable) [IsFiniteMeasure ν] :
    TBoundedSP T hBmeas →ₗ[ℝ] Lp ℝ 2 ν where
  toFun V := (memLp_uncurry_of_isFiniteMeasure hBmeas ν V.val).toLp _
  map_add' V W := by
    change (memLp_uncurry_of_isFiniteMeasure hBmeas ν ((V + W) : TBoundedSP T hBmeas).val).toLp _
      = _
    rw [Submodule.coe_add,
      ← MemLp.toLp_add (memLp_uncurry_of_isFiniteMeasure hBmeas ν V.val)
        (memLp_uncurry_of_isFiniteMeasure hBmeas ν W.val)]
    congr 1
    exact ItoIntegralL2.uncurry_coe_add hBmeas V.val W.val
  map_smul' c V := by
    change (memLp_uncurry_of_isFiniteMeasure hBmeas ν ((c • V) : TBoundedSP T hBmeas).val).toLp _
      = _
    rw [Submodule.coe_smul, RingHom.id_apply,
      ← MemLp.toLp_const_smul c (memLp_uncurry_of_isFiniteMeasure hBmeas ν V.val)]
    congr 1
    exact ItoIntegralL2.uncurry_coe_smul hBmeas c V.val

lemma coeFn_simpleAssemblyOfMeasure (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (ν : @Measure (ℝ≥0 × Ω)
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable) [IsFiniteMeasure ν]
    (V : TBoundedSP T hBmeas) :
    ⇑(simpleAssemblyOfMeasure T hBmeas ν V) =ᵐ[ν] Function.uncurry ⇑V.val :=
  (memLp_uncurry_of_isFiniteMeasure hBmeas ν V.val).coeFn_toLp

/-! ### The bracket weight -/

omit [IsProbabilityMeasure μ] in
/-- `f²·trim_T` is a finite measure exactly when `f ∈ L²(trim_T)`: its total mass is `‖f‖²`. -/
lemma isFiniteMeasure_sqWeight (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {f : ℝ≥0 × Ω → ℝ} (hfL2 : MemLp f 2 (trimMeasure (μ := μ) T hBmeas)) :
    IsFiniteMeasure (sqWeight (trimMeasure (μ := μ) T hBmeas) f) := by
  refine ⟨?_⟩
  have hlt : ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(trimMeasure (μ := μ) T hBmeas) < ⊤ := by
    have h := hfL2.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
      hfL2.aestronglyMeasurable] at h
    have h2 : (∫⁻ z, ‖f z‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂(trimMeasure (μ := μ) T hBmeas)) ≠ ⊤ := by
      intro htop
      rw [htop] at h
      simp [ENNReal.top_rpow_of_pos] at h
    refine lt_of_le_of_ne le_top ?_
    intro htop
    exact h2 (by
      rw [← htop]
      refine lintegral_congr fun z ↦ ?_
      rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast])
  rw [sqWeight, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hlt

/-! ### Density in the bracket-weighted space -/

omit [IsProbabilityMeasure μ] in
/-- The inner product of the rectangle simple process against `g`, taken in the weighted
space, is a set-integral of `f²·g` against `trim_T`. This is where the weight moves from the
measure into the integrand. -/
lemma inner_simpleAssemblyOfMeasure_iocSPHorizon (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {f : ℝ≥0 × Ω → ℝ}
    (hf : Measurable[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable] f)
    [IsFiniteMeasure (sqWeight (trimMeasure (μ := μ) T hBmeas) f)]
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas) a] F)
    (g : Lp ℝ 2 (sqWeight (trimMeasure (μ := μ) T hBmeas) f)) :
    ⟪simpleAssemblyOfMeasure T hBmeas (sqWeight (trimMeasure (μ := μ) T hBmeas) f)
        (iocSPHorizon hBmeas hab hbT hF), g⟫_ℝ
      = ∫ z in Set.Ioc a b ×ˢ F, f z ^ 2 * g z ∂(trimMeasure (μ := μ) T hBmeas) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have hRpred : MeasurableSet (Set.Ioc a b ×ˢ F) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF
  rw [L2.inner_def]
  have h_ae : ∀ᵐ z ∂(sqWeight (trimMeasure (μ := μ) T hBmeas) f),
      (⟪(simpleAssemblyOfMeasure T hBmeas (sqWeight (trimMeasure (μ := μ) T hBmeas) f)
            (iocSPHorizon hBmeas hab hbT hF) : ℝ≥0 × Ω → ℝ) z,
        (g : ℝ≥0 × Ω → ℝ) z⟫_ℝ : ℝ)
        = (Set.Ioc a b ×ˢ F).indicator (fun z ↦ (g : ℝ≥0 × Ω → ℝ) z) z := by
    filter_upwards [coeFn_simpleAssemblyOfMeasure T hBmeas
      (sqWeight (trimMeasure (μ := μ) T hBmeas) f) (iocSPHorizon hBmeas hab hbT hF)] with z hz
    have hSA : (simpleAssemblyOfMeasure T hBmeas (sqWeight (trimMeasure (μ := μ) T hBmeas) f)
        (iocSPHorizon hBmeas hab hbT hF) : ℝ≥0 × Ω → ℝ) z
          = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z := by
      rw [hz, uncurry_iocSPHorizon_eq hBmeas hab hbT hF]
    rw [hSA]
    change (g : ℝ≥0 × Ω → ℝ) z * (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z = _
    by_cases hz_in : z ∈ Set.Ioc a b ×ˢ F
    · rw [Set.indicator_of_mem hz_in, Set.indicator_of_mem hz_in, mul_one]
    · rw [Set.indicator_of_notMem hz_in, Set.indicator_of_notMem hz_in, mul_zero]
  rw [integral_congr_ae h_ae, integral_indicator hRpred, setIntegral_sqWeight hf hRpred]

/-- **Density in the bracket-weighted space.** The simple processes are dense in
`L²(f²·trim_T)`.

The weighted problem reduces to the flat π-λ core by moving the weight into the integrand: a
`g` orthogonal to every simple process makes `h := f²·g` integrate to zero over every
predictable rectangle, `setIntegral_eq_zero_of_orthogonal_pred` promotes that to every
predictable set, and `h = 0` a.e. forces `g = 0` where `f ≠ 0` — which is `f²·trim_T`-a.e.,
that measure being carried by `{f ≠ 0}`. `h` is `L¹` and generally not `L²`, which is why the
core takes an integrable function rather than an `L²` class. -/
theorem simpleAssembly_sqWeight_denseRange (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {f : ℝ≥0 × Ω → ℝ}
    (hf : Measurable[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable] f)
    [IsFiniteMeasure (sqWeight (trimMeasure (μ := μ) T hBmeas) f)] :
    DenseRange (simpleAssemblyOfMeasure T hBmeas
      (sqWeight (trimMeasure (μ := μ) T hBmeas) f)) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  suffices h_orth_bot : (LinearMap.range (simpleAssemblyOfMeasure T hBmeas
      (sqWeight (trimMeasure (μ := μ) T hBmeas) f)))ᗮ = ⊥ by
    rw [denseRange_iff_closure_range,
        ← LinearMap.coe_range (simpleAssemblyOfMeasure T hBmeas
          (sqWeight (trimMeasure (μ := μ) T hBmeas) f)),
        ← Submodule.topologicalClosure_coe,
        Submodule.topologicalClosure_eq_top_iff.mpr h_orth_bot, Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g h_mem
  rw [Submodule.mem_orthogonal] at h_mem
  -- the weight moved into the integrand: `h` is `L¹(trim_T)`, generally not `L²`
  have hgmeas : Measurable[𝓕.predictable] (g : ℝ≥0 × Ω → ℝ) :=
    (Lp.stronglyMeasurable g).measurable
  have hh_meas : AEStronglyMeasurable (fun z ↦ f z ^ 2 * (g : ℝ≥0 × Ω → ℝ) z)
      (trimMeasure (μ := μ) T hBmeas) :=
    (((hf.pow_const 2).mul hgmeas)).aestronglyMeasurable
  have hlint : ∫⁻ z, ‖f z ^ 2 * (g : ℝ≥0 × Ω → ℝ) z‖ₑ ∂(trimMeasure (μ := μ) T hBmeas)
      = ∫⁻ z, ‖(g : ℝ≥0 × Ω → ℝ) z‖ₑ ∂(sqWeight (trimMeasure (μ := μ) T hBmeas) f) := by
    rw [lintegral_sqWeight hf]
    refine lintegral_congr fun z ↦ ?_
    rw [eNorm_mul, eNorm_pow]
  have hh_int : Integrable (fun z ↦ f z ^ 2 * (g : ℝ≥0 × Ω → ℝ) z)
      (trimMeasure (μ := μ) T hBmeas) := by
    refine ⟨hh_meas, ?_⟩
    rw [HasFiniteIntegral, hlint]
    exact ((Lp.memLp g).integrable one_le_two).2
  -- orthogonality on every basic predictable rectangle
  have h_orth : ∀ R ∈ predictableRect (mΩ := mΩ) hBmeas,
      ∫ z in R, f z ^ 2 * (g : ℝ≥0 × Ω → ℝ) z ∂(trimMeasure (μ := μ) T hBmeas) = 0 := by
    intro R hR
    rcases hR with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, _hab, F, hF, rfl⟩
    · have h_R_pred : MeasurableSet[𝓕.predictable] ({(⊥ : ℝ≥0)} ×ˢ F₀) :=
        MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) hF₀
      rw [setIntegral_eq_setIntegral_inter_supp hBmeas _ _ h_R_pred]
      have h_empty : ({(⊥ : ℝ≥0)} ×ˢ F₀) ∩ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) = ∅ := by
        rw [Set.prod_inter_prod,
            show ({(⊥ : ℝ≥0)} ∩ Set.Ioc 0 T : Set ℝ≥0) = ∅ by ext x; simp,
            Set.empty_prod]
      rw [h_empty, setIntegral_empty]
    · have h_R_pred : MeasurableSet[𝓕.predictable] (Set.Ioc a b ×ˢ F) :=
        MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF
      rw [setIntegral_eq_setIntegral_inter_supp hBmeas _ _ h_R_pred]
      have h_inter : (Set.Ioc a b ×ˢ F) ∩ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
          = Set.Ioc (max a 0) (min b T) ×ˢ F := by
        ext ⟨t, ω⟩
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, hω⟩, ⟨h3, h4⟩⟩
          exact ⟨⟨max_lt h1 h3, le_min h2 h4⟩, hω⟩
        · rintro ⟨⟨h1, h2⟩, hω⟩
          refine ⟨⟨⟨(le_max_left _ _).trans_lt h1, h2.trans (min_le_left _ _)⟩, hω⟩, ?_⟩
          exact ⟨(le_max_right _ _).trans_lt h1, h2.trans (min_le_right _ _)⟩
      rw [h_inter, show max a 0 = a from max_eq_left bot_le]
      by_cases hab' : a ≤ min b T
      · have hbT' : min b T ≤ T := min_le_right _ _
        rw [← inner_simpleAssemblyOfMeasure_iocSPHorizon T hBmeas hf hab' hbT' hF g]
        exact h_mem _ ⟨iocSPHorizon hBmeas hab' hbT' hF, rfl⟩
      · push Not at hab'
        rw [Set.Ioc_eq_empty (not_lt.mpr hab'.le), Set.empty_prod, setIntegral_empty]
  -- π-λ core, then a.e. vanishing, then transfer back across the weight
  have hh0 : (fun z ↦ f z ^ 2 * (g : ℝ≥0 × Ω → ℝ) z)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] 0 :=
    hh_int.ae_eq_zero_of_forall_setIntegral_eq_zero
      (fun s hs _ ↦ setIntegral_eq_zero_of_orthogonal_pred T hBmeas hh_int h_orth s hs)
  refine (Lp.eq_zero_iff_ae_eq_zero (f := g)).mpr ?_
  filter_upwards [(withDensity_absolutelyContinuous
      (trimMeasure (μ := μ) T hBmeas) (fun z ↦ ‖f z‖ₑ ^ 2)).ae_le hh0,
    sqWeight_ae_ne_zero (ν := trimMeasure (μ := μ) T hBmeas) hf] with z hz hfz
  have : f z ^ 2 ≠ 0 := pow_ne_zero 2 hfz
  simpa [this] using hz

end PredictableDensityGeneral
end MathFin
