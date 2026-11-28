/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense

/-!
# Infinite-horizon Itô integral on `[0,∞)` as a continuous linear isometry

This file builds the unbounded-horizon Itô integral (the horizon-`T` one,
`ItoIntegralCLM.itoIntegralCLM`, is its restriction to the band `(0,T]`), reusing the finite-horizon
density machinery of `ItoIntegralHorizonDense` via σ-finite exhaustion, delivering the Itô integral
on all of `[0,∞)` as a continuous linear map

`itoIntegralL2 : Lp ℝ 2 trim_full →L[ℝ] Lp ℝ 2 μ`

where `trim_full = (timeMeasure.prod μ).trim 𝓕.predictable_le_prod` is Degenne's
`L2Predictable timeMeasure μ` (kept unfolded for the `Lp` norm instance, as in
`ItoIntegralL2.lean`). This is the σ-finite completion: `timeMeasure` (Lebesgue
on `ℝ≥0`) is infinite, only σ-finite, so the orthogonal-complement density
argument cannot use the finite-measure complement shortcut.

## The mathematical content

The embedding and the Itô isometry on simple processes are already built
(`ItoIntegralL2.simpleAssembly` / `assembly_isometry`). The one remaining step is
**density** of the simple-process embedding in the predictable `L²`. We obtain it
from the *finite-horizon* density machinery (`ItoIntegralHorizonDense`) by a σ-finite
exhaustion of the time axis:

* the basic predictable rectangles `Ioc a b ×ˢ F` / `{0} ×ˢ F₀` are a π-system
  generating the predictable σ-algebra (`ItoIntegralCLM.predictableRect`,
  T-independent — reused verbatim);
* a function `g ∈ L²(trim_full)` orthogonal to every rectangle indicator has
  vanishing set-integral over every rectangle (`itoOrthRect`);
* on each finite frame `Fₙ = Ioc 0 (n+1) ×ˢ univ` the trimmed measure restricts
  to the *finite* `ItoIntegralCLM.trimMeasure (n+1)`
  (`ItoIntegralCLM.trimMeasure_eq_restrict`), so the finite-horizon
  π-λ-induction lemma `ItoIntegralCLM.setIntegral_eq_zero_of_orthogonal_pred`
  applies and forces `g =ᵐ 0` on `Fₙ`;
* the frames cover all of `Ioi 0 ×ˢ univ`, whose complement `{0} ×ˢ univ` is
  `trim_full`-null (`timeMeasure {0} = 0`), so `g =ᵐ[trim_full] 0`.

`LinearMap.extendOfNorm` then yields the CLM and the isometry
`‖itoIntegralL2 f‖ = ‖f‖`.

## Coherence

Pure consumption of the finite-horizon layer + Degenne's `SimpleProcess`
infrastructure; nothing of the π-system or the isometry is reproved. This closes
the unbounded-horizon gap recorded in `docs/archive/ito-integral-clm-deferred.md`.

## Main definitions

* `itoIntegralL2`: the unbounded-horizon Itô integral `Lp ℝ 2 trim_full →L[ℝ] Lp ℝ 2 μ`, the
  extension of `itoAssembly` along the dense `simpleAssembly`.

## Main results

* `simpleAssembly_denseRange`: the image of `simpleAssembly` is dense in the predictable `L²`.
* `itoIntegralL2_norm`: the unbounded-horizon Itô isometry, `‖itoIntegralL2 f‖ = ‖f‖` for every
  `f ∈ Lp 2 trim_full`.
* `itoIntegralL2_simpleAssembly`: on a simple process the `[0,∞)` integral is the explicit
  increment sum `itoSimpleLp V`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 7

## Tags

Itô integral, infinite horizon, stochastic integral, Itô isometry, σ-finite exhaustion,
predictable integrands, MSC 60H05, MSC 60G07
-/

@[expose] public section

open MeasureTheory Filter Topology NNReal ENNReal ProbabilityTheory
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

namespace MathFin
namespace ItoIntegralL2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) [IsProbabilityMeasure μ]

include hB

/-! ### The rectangle indicator as a simple process -/

omit hB [IsProbabilityMeasure μ] in
/-- The simple process realising the indicator of `Ioc a b ×ˢ F` (`F ∈ ℱₐ`), via
upstream `ElementaryPredictableSet.IocProd.indicator`. Unlike `iocSPHorizon` there is
no horizon bound: this is a plain `SimpleProcess`, not a member of the
`T`-bounded submodule. -/
private noncomputable def iocSP (hBmeas : ∀ t, Measurable (B t)) (a b : ℝ≥0) {F : Set Ω}
    (hF : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas) a] F) :
    SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas) :=
  (ElementaryPredictableSet.IocProd a b hF).indicator (1 : ℝ)

omit hB [IsProbabilityMeasure μ] in
/-- The uncurry of `iocSP hBmeas a b hF` is the indicator of `Ioc a b ×ˢ F`. -/
private lemma uncurry_iocSP_eq (hBmeas : ∀ t, Measurable (B t)) (a b : ℝ≥0) {F : Set Ω}
    (hF : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas) a] F) :
    Function.uncurry ⇑(iocSP hBmeas a b hF)
      = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) := by
  funext ⟨t, ω⟩
  change ⇑((ElementaryPredictableSet.IocProd a b hF).indicator (1 : ℝ)) t ω
      = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) (t, ω)
  rw [ElementaryPredictableSet.coe_indicator,
      ElementaryPredictableSet.coe_IocProd a b hF]
  rfl

omit hB in
/-- Inner product of `simpleAssembly (iocSP …)` with `g` is the set-integral of
`g` over the rectangle `Ioc a b ×ˢ F` in `trim_full`. -/
private lemma inner_simpleAssembly_iocSP (hBmeas : ∀ t, Measurable (B t)) (a b : ℝ≥0)
    {F : Set Ω} (hF : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas) a] F)
    (g : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    ⟪simpleAssembly (μ := μ) hBmeas (iocSP hBmeas a b hF), g⟫_ℝ
      = ∫ z in Set.Ioc a b ×ˢ F, g z ∂((timeMeasure.prod μ).trim
          (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration (mΩ := mΩ) hBmeas).predictable
  rw [L2.inner_def]
  have h_coe := MemLp.coeFn_toLp
    (memLp_uncurry_trim (μ := μ) hBmeas (iocSP hBmeas a b hF))
  have h_uncurry_eq := uncurry_iocSP_eq hBmeas a b hF
  have h_ae_eq : ∀ᵐ z ∂((timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod),
      (⟪(simpleAssembly (μ := μ) hBmeas (iocSP hBmeas a b hF) : ℝ≥0 × Ω → ℝ) z,
        (g : ℝ≥0 × Ω → ℝ) z⟫_ℝ : ℝ)
        = (Set.Ioc a b ×ˢ F).indicator (fun z ↦ (g : ℝ≥0 × Ω → ℝ) z) z := by
    filter_upwards [h_coe] with z hz
    have hSA_eq :
        (simpleAssembly (μ := μ) hBmeas (iocSP hBmeas a b hF) : ℝ≥0 × Ω → ℝ) z
          = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z := by
      calc (simpleAssembly (μ := μ) hBmeas (iocSP hBmeas a b hF) : ℝ≥0 × Ω → ℝ) z
          = Function.uncurry ⇑(iocSP hBmeas a b hF) z := hz
        _ = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z := by rw [h_uncurry_eq]
    rw [hSA_eq]
    change (g : ℝ≥0 × Ω → ℝ) z * (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z
        = (Set.Ioc a b ×ˢ F).indicator (fun z ↦ (g : ℝ≥0 × Ω → ℝ) z) z
    by_cases hz_in : z ∈ Set.Ioc a b ×ˢ F
    · rw [Set.indicator_of_mem hz_in, Set.indicator_of_mem hz_in, mul_one]
    · rw [Set.indicator_of_notMem hz_in, Set.indicator_of_notMem hz_in, mul_zero]
  rw [integral_congr_ae h_ae_eq]
  exact integral_indicator
    (MeasureTheory.measurableSet_predictable_Ioc_prod
      (𝓕 := natFiltration (mΩ := mΩ) hBmeas) a b hF)

/-! ### Orthogonality on rectangles -/

omit hB in
/-- A function `g` orthogonal to the range of `simpleAssembly` has vanishing
set-integral over every basic predictable rectangle. The `{0} ×ˢ F₀` piece is
`trim_full`-null (`timeMeasure {0} = 0`); the `Ioc a b ×ˢ F` piece is the inner
product `⟪simpleAssembly (iocSP …), g⟫`, which orthogonality kills. -/
private lemma itoOrthRect (hBmeas : ∀ t, Measurable (B t))
    (g : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod))
    (h_orth : ∀ V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas),
      ⟪simpleAssembly (μ := μ) hBmeas V, g⟫_ℝ = 0) :
    ∀ R ∈ ItoIntegralCLM.predictableRect (mΩ := mΩ) hBmeas,
      ∫ z in R, g z ∂((timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) = 0 := by
  intro R hR
  rcases hR with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, F, _hab, hF, rfl⟩
  · -- `{0} ×ˢ F₀` is `trim_full`-null.
    have hpred : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        ({(0 : ℝ≥0)} ×ˢ F₀) :=
      MeasureTheory.measurableSet_predictable_singleton_bot_prod
        (𝓕 := natFiltration (mΩ := mΩ) hBmeas) hF₀
    have h_null : ((timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)
        ({(0 : ℝ≥0)} ×ˢ F₀) = 0 := by
      rw [trim_measurableSet_eq _ hpred, Measure.prod_prod, timeMeasure_singleton,
          zero_mul]
    exact setIntegral_measure_zero _ h_null
  · -- `Ioc a b ×ˢ F` is the inner product, which orthogonality kills.
    rw [← inner_simpleAssembly_iocSP (μ := μ) hBmeas a b hF g]
    exact h_orth (iocSP hBmeas a b hF)

/-! ### σ-finite exhaustion: orthogonal ⇒ a.e. zero -/

omit hB in
/-- A function `g` orthogonal to the range of `simpleAssembly` is a.e. zero. The
σ-finite exhaustion uses finite frames `Φ n = Ioc 0 (n+1) ×ˢ univ`: on each, the
trim measure restricts to the *finite* `ItoIntegralCLM.trimMeasure (n+1)`
(`trimMeasure_eq_restrict`), where the finite-horizon π-λ-induction lemma
`ItoIntegralCLM.setIntegral_eq_zero_of_orthogonal_pred` forces `g =ᵐ 0`. The
frames cover `Ioi 0 ×ˢ univ`, whose complement `{0} ×ˢ univ` is `trim_full`-null
(`timeMeasure {0} = 0`). -/
private lemma aezeroOfOrth (hBmeas : ∀ t, Measurable (B t))
    (g : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod))
    (h_orth : ∀ V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas),
      ⟪simpleAssembly (μ := μ) hBmeas V, g⟫_ℝ = 0) :
    (g : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod] 0 := by
  let : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration (mΩ := mΩ) hBmeas).predictable
  have h_rect := itoOrthRect (μ := μ) hBmeas g h_orth
  -- predictable-measurability of any rectangle in `predictableRect`
  have hRpred : ∀ R ∈ ItoIntegralCLM.predictableRect (mΩ := mΩ) hBmeas,
      MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable] R := by
    intro R hR
    rw [← ItoIntegralCLM.generateFrom_predictableRect hBmeas]
    exact MeasurableSpace.measurableSet_generateFrom hR
  -- the finite frames
  set Φ : ℕ → Set (ℝ≥0 × Ω) := fun n ↦ Set.Ioc 0 ((n : ℝ≥0) + 1) ×ˢ Set.univ with hΦ
  have hΦ_mem : ∀ n, Φ n ∈ ItoIntegralCLM.predictableRect (mΩ := mΩ) hBmeas := fun n ↦
    Or.inr ⟨0, (n : ℝ≥0) + 1, by positivity, Set.univ, MeasurableSet.univ, rfl⟩
  have hΦ_meas : ∀ n, MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable] (Φ n) :=
    fun n ↦ hRpred _ (hΦ_mem n)
  -- per-frame a.e. zero
  have h_frame : ∀ n : ℕ, (g : ℝ≥0 × Ω → ℝ)
      =ᵐ[((timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod).restrict (Φ n)] 0 := by
    intro n
    have h_bridge : ItoIntegralCLM.trimMeasure (μ := μ) ((n : ℝ≥0) + 1) hBmeas
        = ((timeMeasure.prod μ).trim
          (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod).restrict (Φ n) :=
      ItoIntegralCLM.trimMeasure_eq_restrict (μ := μ) ((n : ℝ≥0) + 1) hBmeas
    rw [← h_bridge]
    -- view `g` as a member of `Lp 2 (trimMeasure (n+1))`
    have hmemn : MemLp (g : ℝ≥0 × Ω → ℝ) 2
        (ItoIntegralCLM.trimMeasure (μ := μ) ((n : ℝ≥0) + 1) hBmeas) := by
      rw [h_bridge]; exact (Lp.memLp g).restrict (Φ n)
    set gₙ := hmemn.toLp (g : ℝ≥0 × Ω → ℝ)
    have hgn_coe : (gₙ : ℝ≥0 × Ω → ℝ)
        =ᵐ[ItoIntegralCLM.trimMeasure (μ := μ) ((n : ℝ≥0) + 1) hBmeas]
          (g : ℝ≥0 × Ω → ℝ) := hmemn.coeFn_toLp
    -- orthogonality of `g` transfers to `trimMeasure (n+1)`
    have h_transfer_g : ∀ R ∈ ItoIntegralCLM.predictableRect (mΩ := mΩ) hBmeas,
        ∫ z in R, (g : ℝ≥0 × Ω → ℝ) z
          ∂(ItoIntegralCLM.trimMeasure (μ := μ) ((n : ℝ≥0) + 1) hBmeas) = 0 := by
      intro R hR
      have h_eq : ∫ z in R, (g : ℝ≥0 × Ω → ℝ) z
            ∂(ItoIntegralCLM.trimMeasure (μ := μ) ((n : ℝ≥0) + 1) hBmeas)
          = ∫ z in R ∩ Φ n, (g : ℝ≥0 × Ω → ℝ) z ∂((timeMeasure.prod μ).trim
              (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) := by
        rw [h_bridge]
        rw [show ∫ z in R, (g : ℝ≥0 × Ω → ℝ) z ∂(((timeMeasure.prod μ).trim
              (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod).restrict (Φ n))
            = ∫ z, (g : ℝ≥0 × Ω → ℝ) z ∂((((timeMeasure.prod μ).trim
              (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod).restrict (Φ n)).restrict R)
            from rfl,
          Measure.restrict_restrict (hRpred R hR)]
      rw [h_eq]
      by_cases hne : (R ∩ Φ n).Nonempty
      · exact h_rect _ (ItoIntegralCLM.isPiSystem_predictableRect hBmeas R hR (Φ n) (hΦ_mem n) hne)
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, setIntegral_empty]
    -- transfer to `gₙ`, then apply the finite-horizon lemma
    have h_transfer : ∀ R ∈ ItoIntegralCLM.predictableRect (mΩ := mΩ) hBmeas,
        ∫ z in R, (gₙ : ℝ≥0 × Ω → ℝ) z
          ∂(ItoIntegralCLM.trimMeasure (μ := μ) ((n : ℝ≥0) + 1) hBmeas) = 0 := by
      intro R hR
      rw [setIntegral_congr_ae (hRpred R hR) (hgn_coe.mono fun z hz _ ↦ hz)]
      exact h_transfer_g R hR
    have hgn0 : (gₙ : ℝ≥0 × Ω → ℝ)
        =ᵐ[ItoIntegralCLM.trimMeasure (μ := μ) ((n : ℝ≥0) + 1) hBmeas] 0 :=
      Lp.ae_eq_zero_of_forall_setIntegral_eq_zero gₙ
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        (fun _ _ _ ↦ ((Lp.memLp gₙ).integrable one_le_two).integrableOn)
        (fun s hs _ ↦ ItoIntegralCLM.setIntegral_eq_zero_of_orthogonal_pred
          (μ := μ) ((n : ℝ≥0) + 1) hBmeas ((Lp.memLp gₙ).integrable one_le_two)
          h_transfer s hs)
    exact hgn_coe.symm.trans hgn0
  -- patch: a.e. zero on every frame + the cover's complement is null ⇒ a.e. zero
  have key : ∀ᵐ z ∂((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod),
      ∀ n : ℕ, z ∈ Φ n → (g : ℝ≥0 × Ω → ℝ) z = (0 : ℝ≥0 × Ω → ℝ) z := by
    rw [ae_all_iff]
    intro n
    exact (ae_restrict_iff' (hΦ_meas n)).mp (h_frame n)
  have hcov : ∀ᵐ z ∂((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod), z ∈ ⋃ n, Φ n := by
    rw [ae_iff]
    have hsub : {z : ℝ≥0 × Ω | z ∉ ⋃ n, Φ n} ⊆ {(0 : ℝ≥0)} ×ˢ Set.univ := by
      intro z hz
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hΦ, Set.mem_prod, Set.mem_Ioc,
        Set.mem_univ, and_true, not_exists, not_and, not_le] at hz
      obtain ⟨t, ω⟩ := z
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
      by_contra ht
      have htpos : 0 < t := by
        rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with h | h
        · exact absurd h.symm ht
        · exact h
      obtain ⟨m, hm⟩ := exists_nat_ge (t : ℝ≥0)
      exact absurd (le_trans hm (le_add_of_nonneg_right zero_le_one)) (not_le.mpr (hz m htpos))
    have hnull : ((timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)
        ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) = 0 := by
      have hpred : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
          ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) :=
        MeasureTheory.measurableSet_predictable_singleton_bot_prod
          (𝓕 := natFiltration (mΩ := mΩ) hBmeas) MeasurableSet.univ
      rw [trim_measurableSet_eq _ hpred, Measure.prod_prod, timeMeasure_singleton, zero_mul]
    exact measure_mono_null hsub hnull
  filter_upwards [key, hcov] with z hz hz_cov
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz_cov
  exact hz n hn

/-! ### Density, the CLM, and the unbounded-horizon isometry -/

omit hB in
/-- **Density**: the image of `simpleAssembly` is dense in the predictable `L²`.
Orthogonal-complement argument: a `g` orthogonal to the range is a.e. zero
(`aezeroOfOrth`). -/
theorem simpleAssembly_denseRange (hBmeas : ∀ t, Measurable (B t)) :
    DenseRange (simpleAssembly (μ := μ) hBmeas) := by
  suffices h_orth_bot :
      (LinearMap.range (simpleAssembly (μ := μ) hBmeas))ᗮ = ⊥ by
    rw [denseRange_iff_closure_range,
        ← LinearMap.coe_range (simpleAssembly (μ := μ) hBmeas),
        ← Submodule.topologicalClosure_coe,
        Submodule.topologicalClosure_eq_top_iff.mpr h_orth_bot, Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g h_mem
  rw [Submodule.mem_orthogonal] at h_mem
  refine (Lp.eq_zero_iff_ae_eq_zero (f := g)).mpr ?_
  exact aezeroOfOrth (μ := μ) hBmeas g (fun V ↦ h_mem _ ⟨V, rfl⟩)

/-- **The unbounded-horizon Itô integral as a CLM.** Built from `itoAssembly`
along the (now dense) `simpleAssembly` via `LinearMap.extendOfNorm`. Its domain
`Lp ℝ 2 trim_full` is Degenne's `L2Predictable timeMeasure μ`. -/
noncomputable def itoIntegralL2 (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) →L[ℝ] Lp ℝ 2 μ :=
  (itoAssembly (μ := μ) hB hBmeas).extendOfNorm (simpleAssembly (μ := μ) hBmeas)

/-- **The unbounded-horizon Itô isometry.** For every `f ∈ Lp 2 trim_full`,
`‖itoIntegralL2 f‖ = ‖f‖`. -/
theorem itoIntegralL2_norm (hBmeas : ∀ t, Measurable (B t))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    ‖itoIntegralL2 (μ := μ) hB hBmeas f‖ = ‖f‖ := by
  rw [itoIntegralL2]
  exact LinearMap.norm_extendOfNorm_eq_of_isometry
    (simpleAssembly_denseRange (μ := μ) hBmeas) (assembly_isometry hB hBmeas) f

/-- **The `[0,∞)` integral of a simple process is its explicit simple integral**
`itoSimpleLp V` (`extendOfNorm` on the dense embedding). -/
lemma itoIntegralL2_simpleAssembly (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V) = itoSimpleLp hB hBmeas V := by
  rw [itoIntegralL2, LinearMap.extendOfNorm_eq (simpleAssembly_denseRange (μ := μ) hBmeas)
    ⟨1, fun W ↦ by rw [one_mul]; exact (assembly_isometry hB hBmeas W).le⟩]
  rfl

end ItoIntegralL2
end MathFin
