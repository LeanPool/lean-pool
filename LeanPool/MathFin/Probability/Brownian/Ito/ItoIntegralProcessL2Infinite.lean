/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral

/-!
# Horizon consistency of the Itô integral process

The unbounded-horizon process `itoProcessL2Inf` (`ItoIntegralProcessL2Inf`) restricted to `[0,T]`
is the finite-horizon `itoProcessCLM T` of the band-restricted integrand
(`itoProcessL2Inf_eq_itoProcessCLM`), by the Itô increment-independence
`E[∫₀^∞ f dB | 𝓕_T] = ∫₀ᵀ f dB`. On the dense simple processes this is concrete, via the
`[0,T]` clamp `clampSP` of a simple process.

## The `[0,∞)` continuous-local-martingale arc

* **step 1** — the L² process: `ItoIntegralProcessL2Inf`;
* **step 2** — horizon consistency: this file;
* **step 3** — the glued continuous modification on `[0,∞)` (the finite gate per
  horizon `T = n`, glued by `indistinguishable_of_modification_on`);
* **step 4** — the `IsLocalMartingale` on the null-augmented filtration (reusing
  `condExp_sup_nulls` / `augFiltration` from the `[0,T]` follow-on).

## Main definitions

* `clampSP`: the `[0,T]` clamp of a simple process.

## Main results

* `clampSP_itoSimpleProcess`: for `t ≤ T` the `[0,T]` clamp of a simple process has the same
  `[0,t]` discrete Itô integral.
* `itoProcessCLM_simpleProcessL2Horizon`: for `t ≤ T`, `itoProcessCLM T t` of a simple process's
  `[0,T]` `L²` integrand is its `[0,t]` discrete Itô integral.
* `itoProcessL2Inf_eq_itoProcessCLM`: for `t ≤ T`, `(f●B)_t = (f|[0,T] ● B)_t`, the
  unbounded-horizon process equals the finite-horizon process of the `[0,T]`-restricted
  integrand.

## Tags

horizon consistency, Itô integral, continuous local martingale, infinite horizon,
stochastic integral, MSC 60H05, MSC 60G44
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessL2Infinite

open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

/-! ### The `[0,T]` clamp of a simple process

The increment-independence crux
`itoIntegralCLM T (simpleProcessL2Horizon T V) =ᵐ itoSimpleProcess V T` cannot be read off the
existing `T`-bounded machinery directly, because a general `V` may carry intervals reaching past
`T`. We clamp `V` to the band: **drop the intervals starting past `T`, clamp every surviving right
endpoint to `T`**. The clamp `clampSP T V` is `T`-bounded, its discrete Itô integral on `[0,t]`
agrees with `V`'s for `t ≤ T`, and its `[0,T]` `L²` integrand agrees with `V`'s — so `V` and its
clamp are indistinguishable to all of the `[0,T]` machinery, which is exactly what closes the
crux. -/

/-- Fiber-sum value of the clamped `mapDomain`: `mapDomain` collapses intervals sharing a
left endpoint, so the value at `p` is the (finite) sum of the original `V`-values over the
clamp-preimage of `p`. The contributors all share `p`'s left endpoint, which keeps the
value `𝓕_{p.1}`-measurable. -/
private lemma clamp_value_apply (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (p : ℝ≥0 × ℝ≥0) (ω : Ω) :
    ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))) p ω
      = ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
          (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0) := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finsupp.support_filter, Finset.mem_filter] at ha
  rw [Finsupp.single_apply]
  by_cases h : (a.1, a.2 ⊓ T) = p
  · simp only [ite_eq_left h, Finsupp.filter_apply_pos (fun q ↦ q.1 ≤ T) V.value ha.2]
  · simp only [ite_eq_right h, Pi.zero_apply]

/-- **The `[0,T]` clamp of a simple process.** -/
noncomputable def clampSP (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas) where
  valueBot := V.valueBot
  value := (V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))
  le_of_mem_support_value := fun p hp ↦ by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    rw [Finsupp.support_filter, Finset.mem_filter] at ha
    exact le_inf (V.le_of_mem_support_value a ha.1) ha.2
  measurable_valueBot := V.measurable_valueBot
  measurable_value' := fun p hp ↦ by
    rw [show ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))) p
          = fun ω ↦ ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
              (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)
        from funext fun ω ↦ clamp_value_apply T hBmeas V p ω]
    refine Finset.measurable_sum _ fun a ha ↦ ?_
    by_cases h : (a.1, a.2 ⊓ T) = p
    · simp only [ite_eq_left h]
      rw [Finsupp.support_filter, Finset.mem_filter] at ha
      have hp1 : a.1 = p.1 := (Prod.ext_iff.mp h).1
      exact hp1 ▸ V.measurable_value a
    · simp only [ite_eq_right h]; exact measurable_const
  bounded_valueBot := V.bounded_valueBot
  bounded_value := by
    refine ⟨(V.value.filter (fun q ↦ q.1 ≤ T)).support.card • |V.valueBound|, fun p hp ω ↦ ?_⟩
    rw [clamp_value_apply]
    calc ‖∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
              (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)‖
        ≤ ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
            ‖(if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support, |V.valueBound| := by
          refine Finset.sum_le_sum fun a ha ↦ ?_
          by_cases h : (a.1, a.2 ⊓ T) = p
          · simp only [ite_eq_left h]
            exact (V.value_le_valueBound a ω).trans (le_abs_self _)
          · simp only [ite_eq_right h, norm_zero]; exact abs_nonneg _
      _ = (V.value.filter (fun q ↦ q.1 ≤ T)).support.card • |V.valueBound| := by
          rw [Finset.sum_const]

/-- **Master `Finsupp.sum` identity for the clamp.** Any additive-in-the-value statistic
`φ` summed over the clamp equals the same statistic summed over `V`, provided `φ` is
invariant under the right-endpoint clamp on the kept intervals (`hclamp`) and vanishes on
the dropped ones (`hdrop`). Both `clampSP_itoSimpleProcess` and `clampSP_simpleProcessL2Horizon`
are instances. -/
private lemma clampSP_value_sum {N : Type*} [AddCommMonoid N] (T : ℝ≥0)
    (hBmeas : ∀ u, Measurable (B u)) (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas))
    (φ : ℝ≥0 × ℝ≥0 → (Ω → ℝ) → N)
    (hφ0 : ∀ p, φ p 0 = 0) (hφadd : ∀ p u v, φ p (u + v) = φ p u + φ p v)
    (hclamp : ∀ a ∈ V.value.support, a.1 ≤ T → φ (a.1, a.2 ⊓ T) (V.value a) = φ a (V.value a))
    (hdrop : ∀ a ∈ V.value.support, T < a.1 → φ a (V.value a) = 0) :
    (clampSP T hBmeas V).value.sum φ = V.value.sum φ := by
  change ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))).sum φ
      = V.value.sum φ
  rw [Finsupp.sum_mapDomain_index hφ0 hφadd, Finsupp.sum, Finsupp.support_filter,
      Finset.sum_filter]
  conv_rhs => rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  by_cases hP : a.1 ≤ T
  · rw [ite_eq_left hP, Finsupp.filter_apply_pos (fun q ↦ q.1 ≤ T) V.value hP]
    exact hclamp a ha hP
  · rw [ite_eq_right hP]
    exact (hdrop a ha (not_le.mp hP)).symm

/-- **Clamp preserves the `[0,t]` discrete Itô integral for `t ≤ T`.** -/
lemma clampSP_itoSimpleProcess (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (ht : t ≤ T) :
    itoSimpleProcess hBmeas (clampSP T hBmeas V) t = itoSimpleProcess hBmeas V t := by
  funext ω
  rw [itoSimpleProcess_apply, itoSimpleProcess_apply]
  refine clampSP_value_sum T hBmeas V (fun p v ↦ v ω * (B (min p.2 t) ω - B (min p.1 t) ω))
    (fun p ↦ by simp) (fun p u v ↦ by simp only [Pi.add_apply]; ring)
    (fun a ha hP ↦ ?_) (fun a ha hP ↦ ?_)
  · rw [show min (a.2 ⊓ T) t = min a.2 t from by rw [min_assoc, min_eq_right ht]]
  · have h1 : min a.1 t = t := min_eq_right (le_of_lt (lt_of_le_of_lt ht hP))
    have h2 : min a.2 t = t :=
      min_eq_right
          (le_of_lt (lt_of_le_of_lt ht (lt_of_lt_of_le hP (V.le_of_mem_support_value a ha))))
    rw [h1, h2, sub_self, mul_zero]

/-- **Clamp agrees with `V` pointwise on the band `(0,T]`.** -/
lemma clampSP_apply (T s : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hsT : s ≤ T) (ω : Ω) :
    (clampSP T hBmeas V) s ω = V s ω := by
  rw [SimpleProcess.apply_eq, SimpleProcess.apply_eq]
  congr 1
  exact clampSP_value_sum T hBmeas V (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) s)
    (fun p ↦ by simp)
    (fun p u v ↦ by
      simp only [Set.indicator_apply, Pi.add_apply]
      split_ifs <;> simp)
    (fun a ha hP ↦ by
      simp only [Set.indicator_apply]
      refine if_congr (Iff.intro (fun h ↦ ⟨h.1, h.2.trans inf_le_left⟩)
        (fun h ↦ ⟨h.1, le_inf h.2 hsT⟩)) rfl rfl)
    (fun a ha hP ↦ by
      rw [Set.indicator_of_notMem]
      rintro ⟨h1, _⟩
      exact absurd (lt_of_le_of_lt hsT hP) (not_lt.mpr h1.le))

/-- **Clamp preserves the `[0,T]` `L²` integrand.** -/
lemma clampSP_simpleProcessL2Horizon (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    simpleProcessL2Horizon (μ := μ) T hBmeas (clampSP T hBmeas V)
      = simpleProcessL2Horizon (μ := μ) T hBmeas V := by
  refine Lp.ext ((MemLp.coeFn_toLp (memLp_uncurry_trimMeasure T hBmeas (clampSP T hBmeas V))).trans
    ((?_ : Function.uncurry ⇑(clampSP T hBmeas V)
        =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry ⇑V).trans
      (MemLp.coeFn_toLp (memLp_uncurry_trimMeasure T hBmeas V)).symm))
  rw [trimMeasure_eq_restrict]
  refine Filter.eventuallyEq_of_mem
    (self_mem_ae_restrict (MeasureTheory.measurableSet_predictable_Ioc_prod
      (𝓕 := natFiltration hBmeas) 0 T MeasurableSet.univ)) (fun z hz ↦ ?_)
  obtain ⟨⟨_, hzT⟩, _⟩ := hz
  exact clampSP_apply T z.1 hBmeas V hzT z.2

/-- **The increment-independence crux (process form).** For `t ≤ T` the finite-horizon
process `itoProcessCLM T t` of `V`'s `[0,T]` `L²` integrand reproduces `V`'s `[0,t]` discrete Itô
integral. Via the clamp: `simpleProcessL2Horizon T V = simpleAssemblyHorizon T (clampSP T V)`
(`clampSP_simpleProcessL2Horizon`), `itoProcessCLM_simpleAssemblyHorizon` then gives `(V'●B)_t` of
the `T`-bounded clamp, which equals `(V●B)_t` (`clampSP_itoSimpleProcess`). -/
lemma itoProcessCLM_simpleProcessL2Horizon (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (ht : t ≤ T) :
    (itoProcessCLM hB T t hBmeas (simpleProcessL2Horizon (μ := μ) T hBmeas V) : Ω → ℝ)
      =ᵐ[μ] itoSimpleProcess hBmeas V t := by
  have hclampT : clampSP T hBmeas V ∈ TBoundedSP T hBmeas := fun p hp ↦ by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    exact inf_le_right
  have hP1 : simpleProcessL2Horizon (μ := μ) T hBmeas V
      = simpleAssemblyHorizon (μ := μ) T hBmeas ⟨clampSP T hBmeas V, hclampT⟩ :=
    (clampSP_simpleProcessL2Horizon T hBmeas V).symm
  rw [hP1, itoProcessCLM_simpleAssemblyHorizon]
  exact clampSP_itoSimpleProcess T t hBmeas V ht ▸
    (memLp_itoSimpleProcess hB hBmeas (clampSP T hBmeas V) t).coeFn_toLp

/-! ## Step 2 — horizon consistency

The crux relating `itoProcessL2Inf` (`[0,∞)`) to `itoProcessCLM` (`[0,T]`) is the **Itô
increment-independence** `E[∫₀^∞ f dB | 𝓕_T] = ∫₀ᵀ f dB`. The `[0,∞)` process restricted to
`[0,T]` is the finite-horizon process of the band-restricted integrand. Both
`f ↦ itoProcessL2Inf t f` and `f ↦ itoProcessCLM T t (restrictToBand T f)` are
continuous-linear in `f` and, on the dense simple processes, both reproduce `V`'s `[0,t]`
discrete Itô integral (`itoProcessL2Inf_simpleAssembly_ae` on the left;
`restrictToBand_simpleAssembly` + `itoProcessCLM_simpleProcessL2Horizon` on the right), so they
agree everywhere. -/

/-- **Horizon consistency.** For `t ≤ T`, the unbounded-horizon process equals the
finite-horizon process of the `[0,T]`-restricted integrand:
`(f●B)_t = (f|[0,T] ● B)_t`. -/
theorem itoProcessL2Inf_eq_itoProcessCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) (ht : t ≤ T)
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    itoProcessL2Inf hB t hBmeas f
      = itoProcessCLM hB T t hBmeas (restrictToBand (μ := μ) T hBmeas f) := by
  refine congrFun (DenseRange.equalizer (simpleAssembly_denseRange (μ := μ) hBmeas)
    (itoProcessL2Inf hB t hBmeas).continuous
    ((itoProcessCLM hB T t hBmeas).comp (restrictToBand (μ := μ) T hBmeas)).continuous
    (funext fun V ↦ ?_)) f
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  refine Lp.ext ?_
  have hLHS := itoProcessL2Inf_simpleAssembly_ae hB t hBmeas V
  have hRHS : (itoProcessCLM hB T t hBmeas
        (restrictToBand (μ := μ) T hBmeas (simpleAssembly hBmeas V)) : Ω → ℝ)
      =ᵐ[μ] itoSimpleProcess hBmeas V t := by
    rw [restrictToBand_simpleAssembly T hBmeas V]
    exact itoProcessCLM_simpleProcessL2Horizon hB T t hBmeas V ht
  exact hLHS.trans hRHS.symm

end ItoIntegralProcessL2Infinite
end MathFin
