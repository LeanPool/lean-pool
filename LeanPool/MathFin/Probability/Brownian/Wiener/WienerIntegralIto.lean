/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralCLM
public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralIndicator

/-!
# The Wiener integral is the Itô integral of a deterministic integrand

`WienerIntegralL2.wienerIntegralLp` (on `L²((0, T])`) and `ItoIntegralCLM.itoIntegralCLM` (on the
predictable `L²` space `Lp ℝ 2 (trimMeasure T)`) are built by the same `extendOfNorm`
construction. This file identifies them: embedding `f ∈ L²((0, T])` as the deterministic process
`(s, ω) ↦ f s` (`detEmbed`, an isometry), the Wiener integral is the Itô integral of that process,

  `wienerIntegralLp B hB T = itoIntegralCLM hB T hBmeas ∘ detEmbed T hBmeas`.

## Main definitions

* `detEmbed`: the isometric embedding `L²((0, T]) → L²(trimMeasure T)` sending a kernel `f` to
  the deterministic process `(s, ω) ↦ f s`.

## Main results

* `wienerIntegralLp_eq_itoIntegralCLM` — the identification of the two continuous linear maps.

## Scope

The bridge needs the measurability hypothesis `hBmeas : ∀ t, Measurable (B t)`, because the Itô side
is defined through the natural filtration of `B`; the Wiener integral does not. It only identifies
the two continuous linear maps on `L²((0, T])`. It does not reprove the Wiener isometry, linearity
or Gaussian law, which stay where they are.

## References

* [B. Oksendal, *Stochastic Differential Equations*][Oksendal2003], §3.1-3.2
* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 7

## Tags

Wiener integral, Itô integral, deterministic integrand, isometric embedding, predictable L2 space,
MSC 60H05, MSC 60J65
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

namespace MathFin
namespace WienerIntegralIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- The coercion `ℝ≥0 → ℝ` carries the time measure `timeMeasureHorizon T` on `(0, T]` to Lebesgue
measure restricted to `(0, T] ⊆ ℝ`. -/
lemma measurePreserving_coe_timeMeasureHorizon (T : ℝ≥0) :
    MeasurePreserving ((↑) : ℝ≥0 → ℝ) (ItoIntegralCLM.timeMeasureHorizon T)
      (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
  refine ⟨measurable_coe_nnreal_real, ?_⟩
  ext A hA
  rw [Measure.map_apply measurable_coe_nnreal_real hA, ItoIntegralCLM.timeMeasureHorizon,
    Measure.restrict_apply (measurable_coe_nnreal_real hA), ItoIntegralL2.timeMeasure,
    ItoIntegralL2.measurableEmbedding_nnrealCoe.comap_apply, Measure.restrict_apply hA]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc]
  constructor
  · rintro ⟨y, ⟨hy, h0, hT⟩, rfl⟩
    exact ⟨hy, by exact_mod_cast h0, by exact_mod_cast hT⟩
  · rintro ⟨hx, h0, hT⟩
    exact ⟨⟨x, h0.le⟩, ⟨hx, by exact_mod_cast h0, by exact_mod_cast hT⟩, rfl⟩

/-- The time coordinate `ℝ≥0 × Ω → ℝ≥0` is measurable for the predictable σ-algebra: every
`(a, ∞) × Ω` is a countable union of basic predictable rectangles `(a, n] × Ω`. -/
lemma measurable_fst_predictable (𝓕 : Filtration ℝ≥0 mΩ) :
    Measurable[𝓕.predictable, inferInstance] (Prod.fst : ℝ≥0 × Ω → ℝ≥0) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  refine measurable_of_Ioi fun a ↦ ?_
  have : (Prod.fst : ℝ≥0 × Ω → ℝ≥0) ⁻¹' Set.Ioi a = ⋃ n : ℕ, Set.Ioc a n ×ˢ (Set.univ : Set Ω) := by
    ext ⟨t, ω⟩
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion, Set.mem_prod, Set.mem_Ioc,
      Set.mem_univ, and_true]
    exact ⟨fun h ↦ (exists_nat_ge t).imp fun n hn ↦ ⟨h, hn⟩, fun ⟨_, h, _⟩ ↦ h⟩
  rw [this]
  exact MeasurableSet.iUnion fun n ↦ measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a n
      MeasurableSet.univ

variable [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- The time coordinate carries the predictable trim `trimMeasure T` to `timeMeasureHorizon T`: the
trim does not change the measure of a set measurable for the coarser σ-algebra, and `μ` is a
probability measure. -/
lemma measurePreserving_fst_trimMeasure (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    @MeasurePreserving _ _ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable _
      Prod.fst (ItoIntegralCLM.trimMeasure (μ := μ) T hBmeas)
          (ItoIntegralCLM.timeMeasureHorizon T) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  refine ⟨measurable_fst_predictable 𝓕, ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_fst_predictable 𝓕) hA, ItoIntegralCLM.trimMeasure,
    trim_measurableSet_eq _ ((measurable_fst_predictable 𝓕) hA), ← Set.prod_univ,
    Measure.prod_prod, measure_univ, mul_one]

/-- **The deterministic integrands inside the Itô space**: the isometry
`L²((0, T]) → L²(trimMeasure T)` sending `f` to the process `(s, ω) ↦ f s`, the composite of
composition with the coercion `ℝ≥0 → ℝ` and with the time coordinate. -/
noncomputable def detEmbed (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T)) →ₗᵢ[ℝ]
      Lp ℝ 2 (ItoIntegralCLM.trimMeasure (μ := μ) T hBmeas) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (measurePreserving_fst_trimMeasure (μ := μ) T hBmeas)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ ((↑) : ℝ≥0 → ℝ) (measurePreserving_coe_timeMeasureHorizon T))


open WienerIntegralL2 ItoIntegralCLM in
/-- The simple process `𝟙_{(lo, hi] × Ω}` is the indicator of the rectangle, trim-a.e. -/
lemma ae_simpleAssemblyHorizon_iocSPHorizon (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (i : StepIndex T) :
    ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas),
      (simpleAssemblyHorizon (μ := μ) T hBmeas
        (iocSPHorizon hBmeas i.2.1 i.2.2 (F := Set.univ) MeasurableSet.univ) : ℝ≥0 × Ω → ℝ) z =
      (Set.Ioc i.1.1 i.1.2 ×ˢ (Set.univ : Set Ω)).indicator (fun _ ↦ (1 : ℝ)) z := by
  filter_upwards [MemLp.coeFn_toLp (memLp_uncurry_trimMeasure (μ := μ) T hBmeas
      (iocSPHorizon hBmeas i.2.1 i.2.2 (F := Set.univ) MeasurableSet.univ).val)] with z hz
  calc _ = Function.uncurry
          ⇑(iocSPHorizon hBmeas i.2.1 i.2.2 (F := Set.univ) MeasurableSet.univ).val z :=
        hz
    _ = _ := by rw [uncurry_iocSPHorizon_eq]

open WienerIntegralL2 ItoIntegralCLM in
/-- The embedded step indicator `𝟙_{(lo, hi]}` is the `T`-bounded simple process
`𝟙_{(lo, hi] × Ω}`. -/
lemma detEmbed_stepIndicatorLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (i : StepIndex T) :
    detEmbed (μ := μ) T hBmeas (stepIndicatorLp T i) =
      simpleAssemblyHorizon (μ := μ) T hBmeas
        (iocSPHorizon hBmeas i.2.1 i.2.2 (F := Set.univ) MeasurableSet.univ) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable
  refine Lp.ext ?_
  have hA := (Lp.coeFn_compMeasurePreserving (p := 2) (stepIndicatorLp T i)
    (measurePreserving_coe_timeMeasureHorizon T)).trans
    ((measurePreserving_coe_timeMeasureHorizon T).quasiMeasurePreserving.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (c := (1 : ℝ)) (hs := i.measurableSet_interval)
        (hμs := i.restrict_interval_ne_top)))
  have hB := (measurePreserving_fst_trimMeasure (μ := μ) T hBmeas).quasiMeasurePreserving.ae_eq_comp
      hA
  have h2 := Lp.coeFn_compMeasurePreserving (p := 2)
    ((Lp.compMeasurePreservingₗᵢ ℝ ((↑) : ℝ≥0 → ℝ) (measurePreserving_coe_timeMeasureHorizon T))
      (stepIndicatorLp T i))
    (measurePreserving_fst_trimMeasure (μ := μ) T hBmeas)
  filter_upwards [h2, hB, ae_simpleAssemblyHorizon_iocSPHorizon (μ := μ) T hBmeas i]
    with z hz2 hz3 hz5
  refine (hz2.trans hz3).trans (Eq.trans ?_ hz5.symm)
  change i.interval.indicator (fun _ ↦ (1 : ℝ)) (z.1 : ℝ) = _
  by_cases h : z.1 ∈ Set.Ioc i.1.1 i.1.2
  · rw [Set.indicator_of_mem (show z ∈ Set.Ioc i.1.1 i.1.2 ×ˢ (Set.univ : Set Ω) from ⟨h, trivial⟩),
      Set.indicator_of_mem (show (z.1 : ℝ) ∈ i.interval from
        ⟨NNReal.coe_lt_coe.2 h.1, NNReal.coe_le_coe.2 h.2⟩)]
  · rw [Set.indicator_of_notMem (show z ∉ Set.Ioc i.1.1 i.1.2 ×ˢ (Set.univ : Set Ω) from
        fun hz ↦ h hz.1),
      Set.indicator_of_notMem (show (z.1 : ℝ) ∉ i.interval from
        fun hh ↦ h ⟨NNReal.coe_lt_coe.1 hh.1, NNReal.coe_le_coe.1 hh.2⟩)]

open WienerIntegralL2 ItoIntegralCLM in
/-- The elementary Itô integral of `𝟙_{(lo, hi] × Ω}` is the Brownian increment `B_hi − B_lo`. -/
lemma itoSimpleLp_iocSPHorizon (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (i : StepIndex T) :
    ItoIntegralL2.itoSimpleLp hB hBmeas
      (iocSPHorizon hBmeas i.2.1 i.2.2 (F := Set.univ) MeasurableSet.univ).val =
        wienerIncrementLp B hB i := by
  refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun ω ↦ ?_)
  have hI : (ElementaryPredictableSet.IocProd i.1.1 i.1.2
      (𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)
      (B := Set.univ) MeasurableSet.univ).I = {(i.1.1, i.1.2)} := ite_eq_left i.2.1
  unfold ItoIntegralL2.itoSimple
  have hsub :
      (iocSPHorizon hBmeas i.2.1 i.2.2 (F := Set.univ) MeasurableSet.univ).val.value.support ⊆
      {(i.1.1, i.1.2)} := fun p hp ↦ by
    by_contra hp_not'
    have hp_not : p ∉ (ElementaryPredictableSet.IocProd i.1.1 i.1.2
      (𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)
      (B := Set.univ) MeasurableSet.univ).I := by rwa [hI]
    apply Finsupp.mem_support_iff.mp hp
    change ((ElementaryPredictableSet.IocProd i.1.1 i.1.2
      (𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)
      (B := Set.univ) MeasurableSet.univ).indicator (1 : ℝ)).value p = 0
    simp [ElementaryPredictableSet.indicator, Finsupp.onFinset_apply, hp_not]
  rw [Finsupp.sum_of_support_subset _ hsub (fun p v ↦ v ω * (B p.2 ω - B p.1 ω))
    (fun p _ ↦ by simp), Finset.sum_singleton]
  simp only [iocSPHorizon, ElementaryPredictableSet.indicator, Finsupp.onFinset_apply, hI,
    Finset.mem_singleton, ite_true]
  change Set.univ.indicator (fun _ ↦ (1 : ℝ)) ω * (B i.1.2 ω - B i.1.1 ω) = _
  simp

open WienerIntegralL2 ItoIntegralCLM in
/-- **The Wiener integral is the Itô integral of the deterministic integrand.** On `L²((0, T])`
the two continuous linear maps agree: `wienerIntegralLp = itoIntegralCLM ∘ detEmbed`. Both are
continuous, they agree on step indicators (each sends `𝟙_{(s, t]}` to `B_t − B_s`), and step
indicators are dense. -/
theorem wienerIntegralLp_eq_itoIntegralCLM (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    wienerIntegralLp B hB T =
      (itoIntegralCLM hB T hBmeas).comp (detEmbed (μ := μ) T hBmeas).toContinuousLinearMap := by
  have key (i : StepIndex T) : wienerIntegralLp B hB T (stepIndicatorLp T i) =
      itoIntegralCLM hB T hBmeas (detEmbed (μ := μ) T hBmeas (stepIndicatorLp T i)) := by
    rw [wienerIntegralLp_stepIndicator, detEmbed_stepIndicatorLp,
      itoIntegralCLM_simpleAssemblyHorizon, itoSimpleLp_iocSPHorizon]
  refine DFunLike.coe_injective <| (stepAssembly_denseRange T).equalizer
    (wienerIntegralLp B hB T).continuous
    ((itoIntegralCLM hB T hBmeas).comp
      (detEmbed (μ := μ) T hBmeas).toContinuousLinearMap).continuous ?_
  refine congrArg DFunLike.coe (Finsupp.lhom_ext
    (φ := (wienerIntegralLp B hB T).toLinearMap ∘ₗ stepAssembly T)
    (ψ := ((itoIntegralCLM hB T hBmeas).comp
      (detEmbed (μ := μ) T hBmeas).toContinuousLinearMap).toLinearMap ∘ₗ stepAssembly T)
    fun i a ↦ ?_)
  simp only [LinearMap.comp_apply, stepAssembly, Finsupp.linearCombination_single,
    ContinuousLinearMap.coe_coe, map_smul, ContinuousLinearMap.comp_apply, key]
  rfl

end WienerIntegralIto
end MathFin
