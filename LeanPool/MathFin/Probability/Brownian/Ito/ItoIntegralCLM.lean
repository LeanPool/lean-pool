/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralL2Dense

/-!
# The horizon-`T` Itô integral is the infinite-horizon one on the band `(0,T]`

`itoIntegralCLM : Lp ℝ 2 trimMeasure →L[ℝ] Lp ℝ 2 μ` is **defined** as the infinite-horizon
Itô integral `itoIntegralL2` (`ItoIntegralL2Dense`) composed with `bandExtend T`, the extension
by zero of a `[0,T]` integrand to the `[0,∞)` predictable `L²` (a linear isometry, with
`restrictToBand T`, the `Lp` inclusion for `trimMeasure T ≤ trim_full`, as left inverse).
There is no second extension argument: linearity, continuity and the isometry
(`itoIntegralCLM_norm`) are those of `itoIntegralL2` and `bandExtend`, and the value on
`T`-bounded simple processes (`itoIntegralCLM_simpleAssemblyHorizon`) is
`bandExtend_simpleAssemblyHorizon` followed by `itoIntegralL2_simpleAssembly`.

The density of the horizon-`T` simple processes (`ItoIntegralHorizonDense`) stays: it is the
engine under `itoIntegralL2`'s own density, and the consumers of this file use it to
reduce statements about `itoIntegralCLM` to simple processes.

## Main definitions

* `monoMeasureLp`: the norm-`≤ 1` inclusion `Lp 2 μ →L[ℝ] Lp 2 ν` for `ν ≤ μ`.
* `restrictToBand`: restriction of a `[0,∞)` predictable integrand to the band `[0,T]`.
* `bandExtend`: extension by zero of a `[0,T]` integrand to the `[0,∞)` predictable `L²`.
* `itoIntegralCLM`: the Itô integral on `[0,T]`, the infinite-horizon `itoIntegralL2` composed
  with `bandExtend`.

## Main results

* `restrictToBand_bandExtend`: `restrictToBand` is a left inverse of `bandExtend`.
* `itoIntegralCLM_simpleAssemblyHorizon`: on a simple embedding the CLM agrees with the elementary
  Itô integral, `itoIntegralCLM (simpleAssemblyHorizon V) = itoSimpleLp V`.
* `itoIntegralCLM_norm`: the Itô isometry on `[0,T]`, `‖itoIntegralCLM f‖ = ‖f‖` for every
  `f ∈ Lp 2 trim_T`.

## Tags

Itô integral, stochastic integral, Itô isometry, continuous linear map, finite horizon,
predictable integrands, MSC 60H05, MSC 60G44
-/

@[expose] public section

open MeasureTheory Filter Topology NNReal ENNReal ProbabilityTheory
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

namespace MathFin
namespace ItoIntegralCLM

open ItoIntegralL2

/-! ### The `Lp` inclusion for `ν ≤ μ` (generic) -/

section MonoMeasureLp
variable {α : Type*} {_mα : MeasurableSpace α} {μ ν : Measure α}

/-- **The `Lp` inclusion for `ν ≤ μ`.** For `f ∈ Lp 2 μ` the *same* function lies in
`Lp 2 ν` with no larger norm (a smaller measure can only shrink the `L²` norm), so
`f ↦ f` is a norm-`≤ 1` continuous linear map `Lp 2 μ →L[ℝ] Lp 2 ν`. Mathlib has
`MemLp.mono_measure` but no packaged CLM; generic measure theory, a natural upstream
candidate. Specialises to measure restriction (`ν = μ.restrict s`, via
`Measure.restrict_le_self`). -/
noncomputable def monoMeasureLp (h : ν ≤ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).mono_measure h).toLp
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_measure h),
          Lp.coeFn_add (((Lp.memLp f).mono_measure h).toLp) (((Lp.memLp g).mono_measure h).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_measure h),
          (Lp.coeFn_add f g).filter_mono (ae_mono h)] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_measure h),
          Lp.coeFn_smul c (((Lp.memLp f).mono_measure h).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h),
          (Lp.coeFn_smul c f).filter_mono (ae_mono h)] with x h1 h2 h3 h4
        simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply] }
    1 (fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top ?_
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h))]
      exact eLpNorm_mono_measure _ h)

@[simp] lemma monoMeasureLp_coeFn (h : ν ≤ μ) (f : Lp ℝ 2 μ) :
    ⇑(monoMeasureLp h f) =ᵐ[ν] ⇑f := by
  simp only [monoMeasureLp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

end MonoMeasureLp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **Restriction of a `[0,∞)` predictable integrand to the band `[0,T]`** as a CLM
`Lp 2 trim_full →L[ℝ] Lp 2 (trimMeasure T)`: the `Lp` inclusion for
`trimMeasure T ≤ trim_full` (the band restriction, `trimMeasure_eq_restrict` +
`Measure.restrict_le_self`). The integrand seen on `[0,T]`. -/
noncomputable def restrictToBand (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)
      →L[ℝ] Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  monoMeasureLp ((trimMeasure_eq_restrict T hBmeas).le.trans Measure.restrict_le_self)

@[simp] lemma restrictToBand_coeFn (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    ⇑(restrictToBand (μ := μ) T hBmeas f) =ᵐ[trimMeasure (μ := μ) T hBmeas] ⇑f :=
  monoMeasureLp_coeFn _ f

/-- **The `[0,T]`-restriction of a simple process's `[0,∞)` assembly is its `[0,T]`
simple-process element** `simpleProcessL2Horizon`. Both are `toLp (uncurry V)` — one against
the full trim, one against the `[0,T]` trim — and `restrictToBand` only re-reads the
*same* function against the smaller measure, so they coincide a.e. on `[0,T]` (where
`trimMeasure` is supported). **No truncation of `V` is needed**: the `[0,T]` element is
literally `V`'s integrand re-measured, not a clamped process. -/
lemma restrictToBand_simpleAssembly (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    restrictToBand (μ := μ) T hBmeas (simpleAssembly hBmeas V)
      = simpleProcessL2Horizon (μ := μ) T hBmeas V := by
  have hmono : trimMeasure (μ := μ) T hBmeas
      ≤ (timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod :=
    (trimMeasure_eq_restrict T hBmeas).le.trans Measure.restrict_le_self
  refine Lp.ext ?_
  calc ⇑(restrictToBand (μ := μ) T hBmeas (simpleAssembly hBmeas V))
      =ᵐ[trimMeasure (μ := μ) T hBmeas] ⇑(simpleAssembly hBmeas V) :=
        restrictToBand_coeFn T hBmeas _
    _ =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry ⇑V :=
        (MemLp.coeFn_toLp (memLp_uncurry_trim hBmeas V)).filter_mono (ae_mono hmono)
    _ =ᵐ[trimMeasure (μ := μ) T hBmeas] ⇑(simpleProcessL2Horizon (μ := μ) T hBmeas V) :=
        (MemLp.coeFn_toLp (memLp_uncurry_trimMeasure T hBmeas V)).symm

/-! ### Extension by zero: the isometric section of `restrictToBand`

A `[0,T]` integrand is a `[0,∞)` integrand carried by the band `(0,T] × Ω`: `bandExtend T` is
that inclusion, and `restrictToBand T` its left inverse. Composing `itoIntegralL2` with it is the
`[0,T]` Itô integral (`itoIntegralCLM_apply`), so horizon consistency
between finite horizons is the equality of two extensions by zero. -/

/-- The predictable trim gives no mass to the time origin `{0} × Ω`. -/
lemma ae_fst_ne_zero_trim (hBmeas : ∀ u, Measurable (B u)) :
    ∀ᵐ z ∂((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod), z.1 ≠ 0 := by
  rw [Filter.eventually_iff, mem_ae_iff,
    show {z : ℝ≥0 × Ω | z.1 ≠ 0}ᶜ = {(⊥ : ℝ≥0)} ×ˢ (Set.univ : Set Ω) from by ext z; simp,
    trim_measurableSet_eq _ (MeasureTheory.measurableSet_predictable_singleton_bot_prod
      (𝓕 := natFiltration (mΩ := mΩ) hBmeas) MeasurableSet.univ),
    Measure.prod_prod, timeMeasure_singleton, zero_mul]

/-- Restricting to the band `(0,T] × Ω` commutes with taking indicators: a.e.-equality in
the `[0,T]` trim lifts to a.e.-equality of the band indicators in the `[0,∞)` trim. -/
lemma indicator_band_ae_eq (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    {f g : ℝ≥0 × Ω → ℝ} (h : f =ᵐ[trimMeasure (μ := μ) T hBmeas] g) :
    (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator f
      =ᵐ[(timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod]
        (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator g := by
  rw [trimMeasure_eq_restrict] at h
  filter_upwards [(ae_restrict_iff'
    (MeasureTheory.measurableSet_predictable_Ioc_prod
      (𝓕 := natFiltration (mΩ := mΩ) hBmeas) 0 T MeasurableSet.univ)).1 h] with z hz
  by_cases hzs : z ∈ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)
  · rw [Set.indicator_of_mem hzs, Set.indicator_of_mem hzs, hz hzs]
  · rw [Set.indicator_of_notMem hzs, Set.indicator_of_notMem hzs]

lemma memLp_indicator_band (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    MemLp ((Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator φ) 2
      ((timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) :=
  (memLp_indicator_iff_restrict (MeasureTheory.measurableSet_predictable_Ioc_prod
      (𝓕 := natFiltration (mΩ := mΩ) hBmeas) 0 T MeasurableSet.univ).nullMeasurableSet).2
    (by rw [← trimMeasure_eq_restrict]; exact Lp.memLp φ)

/-- **Extension by zero** of a `[0,T]` integrand to the `[0,∞)` predictable `L²`: the
isometric section of `restrictToBand`. -/
noncomputable def bandExtend (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) →ₗᵢ[ℝ]
      Lp ℝ 2 ((timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) where
  toFun φ := (memLp_indicator_band T hBmeas φ).toLp
    ((Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator φ)
  map_add' φ ψ := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_band T hBmeas (φ + ψ)),
      Lp.coeFn_add ((memLp_indicator_band T hBmeas φ).toLp _)
        ((memLp_indicator_band T hBmeas ψ).toLp _),
      MemLp.coeFn_toLp (memLp_indicator_band T hBmeas φ),
      MemLp.coeFn_toLp (memLp_indicator_band T hBmeas ψ),
      indicator_band_ae_eq T hBmeas (Lp.coeFn_add φ ψ)] with z h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, Set.indicator_add']
  map_smul' c φ := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_band T hBmeas (c • φ)),
      Lp.coeFn_smul c ((memLp_indicator_band T hBmeas φ).toLp _),
      MemLp.coeFn_toLp (memLp_indicator_band T hBmeas φ),
      indicator_band_ae_eq T hBmeas (Lp.coeFn_smul c φ)] with z h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply]
    by_cases hz : z ∈ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.smul_apply]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, smul_zero]
  norm_map' φ := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def,
        eLpNorm_indicator_eq_eLpNorm_restrict
      (MeasureTheory.measurableSet_predictable_Ioc_prod
        (𝓕 := natFiltration (mΩ := mΩ) hBmeas) 0 T MeasurableSet.univ).nullMeasurableSet,
      ← trimMeasure_eq_restrict]

lemma bandExtend_coeFn (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ⇑(bandExtend T hBmeas φ) =ᵐ[(timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod]
      (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator ⇑φ :=
  MemLp.coeFn_toLp (memLp_indicator_band T hBmeas φ)

/-- `restrictToBand` is a left inverse of `bandExtend`: a `[0,T]` integrand is unchanged by
extending it by zero and restricting back. -/
lemma restrictToBand_bandExtend (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    restrictToBand (μ := μ) T hBmeas (bandExtend T hBmeas φ) = φ := by
  refine Lp.ext ?_
  filter_upwards [restrictToBand_coeFn T hBmeas (bandExtend T hBmeas φ),
    (bandExtend_coeFn T hBmeas φ).filter_mono
      (ae_mono ((trimMeasure_eq_restrict T hBmeas).le.trans Measure.restrict_le_self)),
    ae_fst_mem_Ioc_trimMeasure (μ := μ) T hBmeas] with z h1 h2 h3
  rw [h1, h2]
  exact Set.indicator_of_mem (show z ∈ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) from
    ⟨h3, Set.mem_univ _⟩) _

/-- A class carried by `(0,T] × Ω`, extended by zero, is the same function read in the
`[0,∞)` trim. -/
lemma bandExtend_toLp_ae_eq (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) {g : ℝ≥0 × Ω → ℝ}
    (hg0 : ∀ z : ℝ≥0 × Ω, T < z.1 → g z = 0)
    (hgm : MemLp g 2 (trimMeasure (μ := μ) T hBmeas)) :
    ⇑(bandExtend T hBmeas (hgm.toLp g)) =ᵐ[(timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod] g := by
  filter_upwards [bandExtend_coeFn T hBmeas (hgm.toLp g),
    indicator_band_ae_eq T hBmeas hgm.coeFn_toLp, ae_fst_ne_zero_trim hBmeas] with z h1 h2 h0
  rw [h1, h2]
  by_cases hz : z.1 ≤ T
  · exact Set.indicator_of_mem (show z ∈ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) from
    ⟨⟨pos_iff_ne_zero.2 h0, hz⟩, Set.mem_univ _⟩) _
  · rw [Set.indicator_of_notMem (show z ∉ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) from fun h ↦ hz h.1.2),
      hg0 z (not_le.1 hz)]

/-- On a `T`-bounded simple process, extension by zero turns the `[0,T]` embedding into the
`[0,∞)` one. -/
lemma bandExtend_simpleAssemblyHorizon (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP T hBmeas) :
    bandExtend T hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V) =
      simpleAssembly hBmeas V.val := by
  refine Lp.ext ?_
  filter_upwards [bandExtend_coeFn T hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V),
    indicator_band_ae_eq T hBmeas (memLp_uncurry_trimMeasure (μ := μ) T hBmeas V.val).coeFn_toLp,
    (memLp_uncurry_trim (μ := μ) hBmeas V.val).coeFn_toLp,
    ae_fst_ne_zero_trim hBmeas] with z h1 h2 h3 h0
  refine h1.trans (h2.trans (Eq.trans ?_ h3.symm))
  rcases z with ⟨t, ω⟩
  by_cases ht : t ≤ T
  · exact Set.indicator_of_mem (show (t, ω) ∈ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) from
    ⟨⟨pos_iff_ne_zero.2 h0, ht⟩, Set.mem_univ _⟩) _
  · rw [Set.indicator_of_notMem
      (show (t, ω) ∉ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) from fun h ↦ ht h.1.2)]
    exact (uncurry_eq_zero_of_lt V (not_le.1 ht) ω).symm

/-! ### The CLM `itoIntegralCLM` and its isometry -/

/-- **The Itô integral on `[0,T]`**: the infinite-horizon integral `itoIntegralL2` of the
integrand extended by zero (`bandExtend`). A continuous linear map as a composite of one. -/
noncomputable def itoIntegralCLM (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 μ :=
  (itoIntegralL2 hB hBmeas).comp (bandExtend T hBmeas).toContinuousLinearMap

theorem itoIntegralCLM_apply (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    itoIntegralCLM hB T hBmeas φ = itoIntegralL2 hB hBmeas (bandExtend T hBmeas φ) :=
  rfl

/-- **The CLM agrees with the elementary Itô integral on a simple embedding**:
`itoIntegralCLM (simpleAssemblyHorizon V) = itoSimpleLp V`. The bridge every consumer of the CLM
crosses to get back to the finite increment sum `∑ V(p)·(B_{p.2} − B_{p.1})`: it is what makes
`DenseRange.equalizer` arguments over `simpleAssemblyHorizon_denseRange` computable at all. -/
theorem itoIntegralCLM_simpleAssemblyHorizon (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (V : TBoundedSP T hBmeas) :
    itoIntegralCLM hB T hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V)
      = ItoIntegralL2.itoSimpleLp hB hBmeas V.val := by
  rw [itoIntegralCLM_apply, bandExtend_simpleAssemblyHorizon, itoIntegralL2_simpleAssembly]

/-- **The continuous-time Itô isometry on `[0,T]`.** For every
`f ∈ Lp 2 trim_T`, `‖itoIntegralCLM f‖ = ‖f‖`. -/
theorem itoIntegralCLM_norm (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (f : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖itoIntegralCLM hB T hBmeas f‖ = ‖f‖ := by
  rw [itoIntegralCLM_apply, itoIntegralL2_norm, LinearIsometry.norm_map]

end ItoIntegralCLM
end MathFin
