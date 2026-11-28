/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralCLM
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessL2Inf

/-! # The general-integrand Itô integral as an L² martingale on `[0,T]` (B1b)

B1a built the simple-integrand Itô integral `t ↦ (V●B)_t` as a continuous L²
martingale. This file extends it to a **general** predictable integrand
`φ ∈ Lp ℝ 2 (trimMeasure T)` (= Degenne's `L2Predictable` on `[0,T]`): the process
`t ↦ (φ●B)_t := ∫₀ᵗ φ dB` is an L² martingale (a.e.-adapted; no path continuity is claimed
here), with the Itô contraction `‖(φ●B)_t‖ ≤ ‖φ‖` and the terminal Itô isometry
`‖(φ●B)_T‖ = ‖φ‖`. The explicit time-indexed isometry
`E[(φ●B)_t²] = ∫₀ᵗ E[φ_s²] ds` is proved in the companion module
`ItoIntegralProcessIsometry` (`itoProcessCLM_norm_sq`), by density-transferring the
band-restricted simple-process isometry against a band-truncation CLM.

The process is *defined* as the infinite-horizon process `itoProcessL2Inf`
(`ItoIntegralProcessL2Inf`) composed with `bandExtend`, i.e. as the `𝓕_t`-conditional-expectation
projection (`condExpL2`) of the terminal integral `itoIntegralCLM`; its martingale property,
adaptedness and the contraction `‖(φ●B)_t‖ ≤ ‖φ‖` are those of the infinite-horizon engine, proved
there once. The bridge to B1a's simple-integrand process (`itoProcessCLM_simpleAssemblyHorizon`) is
B1a's martingale property.

## Main definitions

* `itoProcessCLM`: the Itô integral process `(φ●B)_t = ∫₀ᵗ φ dB` on `[0,T]`, the `𝓕_t`
  conditional-expectation projection (`condExpL2`) of the terminal integral `itoIntegralCLM`.

## Main results

* `itoProcessCLM_simpleAssemblyHorizon` — the bridge back to B1a.
* `itoProcessCLM_zero_time` — the process starts at `0` (inherited from the infinite-horizon
  engine, `itoProcessL2Inf_zero_time`).
* `itoProcessCLM_eq_condExpL2` — **the key identity** (by definition): `(φ●B)_t` is the
  `𝓕_t`-projection of the terminal integral.
* `itoProcessCLM_aeStronglyMeasurable`, `itoIntegralProcessGen_isMartingale` — its two
  corollaries: a.e.-adaptedness and the martingale property.
* `itoProcessCLM_norm_le` — the contraction `‖(φ●B)_t‖ ≤ ‖φ‖`.
* `itoProcessCLM_terminal_eq`, `itoProcessCLM_norm_terminal` — at the horizon the process is
  the terminal integral, so the contraction is the Itô isometry.
* `integral_itoIntegralCLM` — the terminal integral is centered.
* `itoIntegralProcessGen_l2_continuous` — `t ↦ (φ●B)_t` is `L²`-continuous.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 7

## Tags

Itô integral process, L² martingale, Itô isometry, stochastic integral, predictable integrand,
conditional expectation, MSC 60H05, MSC 60G44
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralProcessGeneral

open MeasureTheory ProbabilityTheory
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessL2Infinite
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **The Itô integral process on `[0,T]`**: the `𝓕_t`-conditional-expectation projection
(`condExpL2`) of the terminal integral `itoIntegralCLM`. For `φ ∈ L²(predictable, [0,T])`, this
is `∫₀ᵗ φ dB ∈ L²(μ)`; it is the band restriction `itoProcessL2Inf t ∘ bandExtend T` of the
infinite-horizon process. -/
noncomputable def itoProcessCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 μ :=
  (itoProcessL2Inf hB t hBmeas).comp (bandExtend T hBmeas).toContinuousLinearMap

/-- **The key identity.** The general Itô integral at time `t` is the
conditional-expectation projection of its terminal value `∫₀ᵀ φ dB` onto `𝓕_t`:
`(φ●B)_t = condExpL2 𝓕_t (itoIntegralCLM T φ)`. Adaptedness and the martingale
property are corollaries. -/
theorem itoProcessCLM_eq_condExpL2 (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    itoProcessCLM hB T t hBmeas φ
      = (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t)
          (itoIntegralCLM hB T hBmeas φ) : Lp ℝ 2 μ) :=
  rfl

/-- **The bridge to B1a.** On the embedding of a `T`-bounded simple process, the general CLM
reproduces B1a's t-process `(V●B)_t`: on simple processes the terminal integral is `itoSimple V`
and B1a's martingale reads `μ[itoSimple V | 𝓕_t] = (V●B)_t`. -/
theorem itoProcessCLM_simpleAssemblyHorizon (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP T hBmeas) :
    itoProcessCLM hB T t hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V)
      = itoSimpleProcessLp hB hBmeas V.val t := by
  rw [itoProcessCLM_eq_condExpL2, itoIntegralCLM_simpleAssemblyHorizon]
  refine Lp.ext ?_
  simp only [itoSimpleProcessLp, itoSimpleLp]
  filter_upwards [(memLp_itoSimpleProcess hB hBmeas V.val t).coeFn_toLp,
    (memLp_itoSimple hB hBmeas V.val).condExpL2_ae_eq_condExp (𝕜 := ℝ)
        ((natFiltration hBmeas).le t),
    condExp_itoSimple_eq hB T t hBmeas V.val V.property] with ω hω1 hω2 hω3
  rw [hω2, hω3, hω1]

/-- **The Itô integral process starts at zero**: it is the infinite-horizon process, which does
(`itoProcessL2Inf_zero_time`), at the band extension of the integrand. -/
@[simp] theorem itoProcessCLM_zero_time (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    itoProcessCLM hB T 0 hBmeas φ = 0 :=
  itoProcessL2Inf_zero_time hB hBmeas _

/-- **a.e.-adaptedness.** `(φ●B)_t` is a.e. `𝓕_t`-measurable: it is the `condExpL2`
projection onto the `𝓕_t`-measurable subspace (`itoProcessL2Inf_aeStronglyMeasurable`). -/
theorem itoProcessCLM_aeStronglyMeasurable (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    AEStronglyMeasurable[natFiltration hBmeas t]
      (itoProcessCLM hB T t hBmeas φ : Ω → ℝ) μ :=
  itoProcessL2Inf_aeStronglyMeasurable hB t hBmeas (bandExtend T hBmeas φ)

/-- **The general Itô integral is an L² martingale (B1b).** For `i ≤ j`,
`μ[(φ●B)_j | 𝓕_i] =ᵐ (φ●B)_i`: the martingale property of the infinite-horizon process
(`itoProcessL2Inf_isMartingale`), the conditional-expectation tower for `∫₀ᵀ φ dB`. -/
theorem itoIntegralProcessGen_isMartingale (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {i j : ℝ≥0} (hij : i ≤ j) :
    μ[(itoProcessCLM hB T j hBmeas φ : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] (itoProcessCLM hB T i hBmeas φ : Ω → ℝ) :=
  itoProcessL2Inf_isMartingale hB hBmeas (bandExtend T hBmeas φ) hij

/-- **The Itô-isometry contraction.** `‖(φ●B)_t‖ ≤ ‖φ‖`: conditional expectation is an L²
contraction (`itoProcessL2Inf_norm_le`) and `bandExtend` is an isometry. -/
theorem itoProcessCLM_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖itoProcessCLM hB T t hBmeas φ‖ ≤ ‖φ‖ :=
  (itoProcessL2Inf_norm_le hB t hBmeas (bandExtend T hBmeas φ)).trans_eq
    (LinearIsometry.norm_map _ _)

/-- **At the terminal time the process is the terminal integral.** `(φ●B)_T = itoIntegralCLM φ`
as `Lp` elements: both are continuous-linear in `φ` and reproduce `itoSimple V` on the dense
simple processes (`(V●B)_T = itoSimple V`). -/
theorem itoProcessCLM_terminal_eq (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    itoProcessCLM hB T T hBmeas φ = itoIntegralCLM hB T hBmeas φ :=
  congrFun (DenseRange.equalizer (simpleAssemblyHorizon_denseRange (μ := μ) T hBmeas)
    (itoProcessCLM hB T T hBmeas).continuous (itoIntegralCLM hB T hBmeas).continuous
    (funext fun V ↦ by
      simp only [Function.comp_apply, itoProcessCLM_simpleAssemblyHorizon,
        itoIntegralCLM_simpleAssemblyHorizon, itoSimpleProcessLp, itoSimpleLp,
        itoSimpleProcess_eq_itoSimple hBmeas V.val (fun p hp ↦ V.property p hp)])) φ

/-- **Terminal Itô isometry.** At the horizon the process is the terminal integral
(`itoProcessCLM_terminal_eq`), so `‖(φ●B)_T‖ = ‖φ‖` exactly. -/
theorem itoProcessCLM_norm_terminal (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖itoProcessCLM hB T T hBmeas φ‖ = ‖φ‖ := by
  rw [itoProcessCLM_terminal_eq hB T hBmeas φ, itoIntegralCLM_norm hB T hBmeas φ]

/-- **The Itô integral is centered**, `𝔼[∫₀ᵀ φ dB] = 0`: the integral process is a
martingale started at `0`, and conditioning preserves the mean. -/
theorem integral_itoIntegralCLM (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∫ ω, itoIntegralCLM hB T hBmeas φ ω ∂μ = 0 := by
  have hmart := itoIntegralProcessGen_isMartingale hB T hBmeas φ (i := 0) (j := T) zero_le
  rw [itoProcessCLM_zero_time hB T hBmeas φ] at hmart
  rw [← itoProcessCLM_terminal_eq hB T hBmeas φ,
    ← integral_condExp ((natFiltration hBmeas).le 0), integral_congr_ae hmart]
  simp

/-- **L²-continuity.** `t ↦ (φ●B)_t` is continuous into `Lp ℝ 2 μ`. The simple-
process integrals `t ↦ (Vₙ●B)_t` (continuous by B1a's
`itoSimpleProcessLp_l2_continuous`) approximate it *uniformly in `t`* — the
contraction `‖(φ●B)_t − (Vₙ●B)_t‖ ≤ ‖φ − Vₙ‖` is `t`-free — so the limit is
continuous (`TendstoUniformly.continuous`). -/
theorem itoIntegralProcessGen_l2_continuous (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Continuous (fun t ↦ itoProcessCLM hB T t hBmeas φ) := by
  -- approximate `φ` by a sequence of simple-process embeddings (dense range).
  obtain ⟨g, hg_range, hg_lim⟩ := mem_closure_iff_seq_limit.mp
    ((simpleAssemblyHorizon_denseRange (μ := μ) T hBmeas).closure_range.ge (Set.mem_univ φ))
  choose V hV using hg_range
  -- each approximant's process is continuous in `t` (bridge to B1a's continuity).
  have hcont_n : ∀ n, Continuous (fun t ↦ itoProcessCLM hB T t hBmeas (g n)) := fun n ↦ by
    simp only [← hV n, itoProcessCLM_simpleAssemblyHorizon]
    exact itoSimpleProcessLp_l2_continuous hB hBmeas (V n).val
  -- uniform convergence: `dist ≤ ‖φ − gₙ‖ → 0`, independent of `t`.
  have huniform : TendstoUniformly (fun n t ↦ itoProcessCLM hB T t hBmeas (g n))
      (fun t ↦ itoProcessCLM hB T t hBmeas φ) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hnorm_lim : Filter.Tendsto (fun n ↦ ‖φ - g n‖) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := φ)).sub hg_lim
      simpa using this.norm
    filter_upwards [hnorm_lim.eventually (eventually_lt_nhds hε)] with n hn t
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt (itoProcessCLM_norm_le hB T t hBmeas (φ - g n)) hn
  exact huniform.continuous (Filter.Eventually.of_forall hcont_n).frequently

omit hB [IsProbabilityMeasure μ] in
/-- **A `timeMeasure` integral over `(0, T]` is an interval integral over `[0, T]`.** For every
`g : ℝ≥0 → ℝ`, `∫ s in Ioc 0 T, g s ∂timeMeasure = ∫ x in 0..T, g x.toNNReal`. Since
`timeMeasure = Measure.comap ((↑) : ℝ≥0 → ℝ) volume`, this is a change of variables along the
coercion (`MeasurableEmbedding.restrict_comap`, `.map_comap`, `.integral_map`) followed by
`intervalIntegral.integral_of_le`, so it needs no measurability or integrability hypothesis. -/
theorem timeMeasure_Ioc_eq_interval {g : ℝ≥0 → ℝ} (T : ℝ≥0) :
    ∫ s in Set.Ioc 0 T, g s ∂timeMeasure = ∫ x in (0)..(T : ℝ), g (Real.toNNReal x) := by
  have himg : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc 0 T = Set.Ioc 0 (T : ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨mod_cast hy1, mod_cast hy2⟩
    · rintro ⟨hx1, hx2⟩
      have hy : (Real.toNNReal x : ℝ) = x := Real.coe_toNNReal x hx1.le
      exact ⟨Real.toNNReal x, ⟨Real.toNNReal_pos.2 hx1, NNReal.coe_le_coe.1 (hy.trans_le hx2)⟩, hy⟩
  have hmap : Measure.map ((↑) : ℝ≥0 → ℝ) (timeMeasure.restrict (Set.Ioc 0 T))
      = volume.restrict (((↑) : ℝ≥0 → ℝ) '' Set.Ioc 0 T) := by
    rw [timeMeasure, MeasurableEmbedding.restrict_comap measurableEmbedding_nnrealCoe,
      MeasurableEmbedding.map_comap measurableEmbedding_nnrealCoe,
      Measure.restrict_restrict measurableEmbedding_nnrealCoe.measurableSet_range,
      Set.inter_eq_right.2 (Set.image_subset_range _ _)]
  calc ∫ s in Set.Ioc 0 T, g s ∂timeMeasure
      = ∫ x, g (Real.toNNReal x) ∂(timeMeasure.restrict (Set.Ioc 0 T)) :=
        integral_congr_ae (.of_forall fun x ↦ by simp only [Real.toNNReal_coe])
    _ = ∫ y, g (Real.toNNReal y) ∂(Measure.map ((↑) : ℝ≥0 → ℝ)
          (timeMeasure.restrict (Set.Ioc 0 T))) :=
        (measurableEmbedding_nnrealCoe.integral_map fun y : ℝ ↦ g (Real.toNNReal y)).symm
    _ = ∫ x in Set.Ioc 0 (T : ℝ), g (Real.toNNReal x) := by rw [hmap, himg]
    _ = ∫ x in (0)..(T : ℝ), g (Real.toNNReal x) :=
        (intervalIntegral.integral_of_le (NNReal.coe_nonneg T)).symm

end ItoIntegralProcessGeneral
end MathFin
