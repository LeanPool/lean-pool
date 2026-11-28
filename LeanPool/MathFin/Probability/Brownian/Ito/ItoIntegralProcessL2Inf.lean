/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralL2Dense
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessMartingale

/-!
# The unbounded-horizon Itô integral as an L² process

B2 (`ItoIntegralL2Dense`) built the **terminal** `[0,∞)` Itô integral
`itoIntegralL2 : Lp 2 trim_full →L[ℝ] Lp 2 μ` over the **horizon-independent**
predictable integrand `f` (the σ-finite completion). This file lifts it to a
**process** `itoProcessL2Inf t f := E[∫₀^∞ f dB | 𝓕_t]` — the
conditional-expectation projection of the terminal integral onto the natural
filtration `𝓕_t`.

Because the integrand no longer depends on the horizon, the L² **martingale
property** (`itoProcessL2Inf_isMartingale`), **adaptedness**
(`itoProcessL2Inf_aeStronglyMeasurable`) and the **contraction**
(`itoProcessL2Inf_norm_le`) hold on all of `ℝ≥0` directly from the conditional-expectation
tower, once. The finite-horizon process `itoProcessCLM T t` (`ItoIntegralProcessGeneral`) is
this engine composed with `bandExtend T`, and inherits all three.

On the dense simple integrands the process is B1a's discrete process
(`condExp_itoSimple_eq`, `condExp_itoIntegralL2_simple`, `itoProcessL2Inf_simpleAssembly_ae`),
and density transfers the start `(f●B)_0 = 0` (`itoProcessL2Inf_zero_time`).

## Main definitions

* `itoProcessL2Inf`: the unbounded-horizon Itô process `(f●B)_t = E[∫₀^∞ f dB | 𝓕_t]`, the
  conditional-expectation projection of `itoIntegralL2 f` onto `𝓕_t`.

## Main results

* `itoProcessL2Inf_isMartingale`: for `i ≤ j`, `E[(f●B)_j | 𝓕_i] =ᵐ (f●B)_i`.
* `itoProcessL2Inf_aeStronglyMeasurable`: `(f●B)_t` is almost everywhere `𝓕_t`-measurable.
* `itoProcessL2Inf_norm_le`: `‖(f●B)_t‖ ≤ ‖f‖`.
* `condExp_itoSimple_eq`: for `T`-bounded `V`, `μ[itoSimple V | 𝓕_t] = (V●B)_t`.
* `itoProcessL2Inf_zero_time`: `(f●B)_0 = 0`.

## Tags

Itô integral process, infinite horizon, L² martingale, conditional expectation, stochastic integral,
MSC 60H05, MSC 60G44
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessL2Infinite

open ItoIntegralL2 ItoIntegralProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

/-- **The unbounded-horizon Itô process** `(f●B)_t = E[∫₀^∞ f dB | 𝓕_t]`: the
conditional-expectation projection of the terminal `[0,∞)` integral `itoIntegralL2 f`
onto `𝓕_t`. The horizon-independent analogue of `itoProcessCLM`. -/
noncomputable def itoProcessL2Inf (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) →L[ℝ] Lp ℝ 2 μ :=
  ((lpMeas ℝ ℝ (natFiltration hBmeas t) 2 μ).subtypeL.comp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t))).comp (itoIntegralL2 hB hBmeas)

/-- Unfold of the process to the `condExpL2` projection of the terminal integral
(coerced from the `𝓕_t`-measurable subspace into `Lp 2 μ`). -/
lemma itoProcessL2Inf_apply (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    itoProcessL2Inf hB t hBmeas f
      = (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f) : Lp ℝ 2 μ) :=
  rfl

/-- **The unbounded-horizon Itô process is an L² martingale.** For `i ≤ j`,
`E[(f●B)_j | 𝓕_i] =ᵐ (f●B)_i` — directly from the conditional-expectation tower,
since each value is `E[∫₀^∞ f dB | 𝓕_k]`. -/
theorem itoProcessL2Inf_isMartingale (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) {i j : ℝ≥0} (hij : i ≤ j) :
    μ[(itoProcessL2Inf hB j hBmeas f : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] (itoProcessL2Inf hB i hBmeas f : Ω → ℝ) := by
  have hbridge : ∀ k : ℝ≥0,
      (itoProcessL2Inf hB k hBmeas f : Ω → ℝ)
        =ᵐ[μ] μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas k] := by
    intro k
    rw [itoProcessL2Inf_apply]
    have h := (Lp.memLp (itoIntegralL2 hB hBmeas f)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((natFiltration hBmeas).le k)
    rwa [Lp.toLp_coeFn] at h
  calc μ[(itoProcessL2Inf hB j hBmeas f : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] μ[μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas j]
              | natFiltration hBmeas i] := condExp_congr_ae (hbridge j)
    _ =ᵐ[μ] μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas i] :=
        condExp_condExp_of_le ((natFiltration hBmeas).mono hij) ((natFiltration hBmeas).le j)
    _ =ᵐ[μ] (itoProcessL2Inf hB i hBmeas f : Ω → ℝ) := (hbridge i).symm

/-- **a.e.-adaptedness.** `(f●B)_t` is a.e. `𝓕_t`-measurable: it is the `condExpL2`
projection onto the `𝓕_t`-measurable subspace. -/
theorem itoProcessL2Inf_aeStronglyMeasurable (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    AEStronglyMeasurable[natFiltration hBmeas t]
      (itoProcessL2Inf hB t hBmeas f : Ω → ℝ) μ := by
  rw [itoProcessL2Inf_apply]
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f)).2

/-- **The Itô-isometry contraction.** `‖(f●B)_t‖ ≤ ‖f‖`: conditional expectation is
an L² contraction and the terminal integral is an isometry (`itoIntegralL2_norm`). -/
theorem itoProcessL2Inf_norm_le (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    ‖itoProcessL2Inf hB t hBmeas f‖ ≤ ‖f‖ := by
  rw [itoProcessL2Inf_apply]
  exact (norm_condExpL2_le ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f)).trans
    (itoIntegralL2_norm hB hBmeas f).le

omit [IsProbabilityMeasure μ] in
include hB in
/-- B1a's martingale to the terminal: `μ[itoSimple V | 𝓕_t] = (V●B)_t` for
`T`-bounded `V` (`(V●B)_{T'} = itoSimple V` at `T' = t ⊔ T`). -/
theorem condExp_itoSimple_eq (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (hVT : ∀ p ∈ V.value.support, p.2 ≤ T) :
    μ[itoSimple hBmeas V | natFiltration hBmeas t]
      =ᵐ[μ] fun ω ↦ itoSimpleProcess hBmeas V t ω := by
  have hT'eq : itoSimpleProcess hBmeas V (max t T) = itoSimple hBmeas V :=
    itoSimpleProcess_eq_itoSimple hBmeas V fun p hp ↦ (hVT p hp).trans (le_max_right t T)
  simpa only [hT'eq] using (itoSimpleProcess_isMartingale hB hBmeas V).2 t (max t T)
      (le_max_left t T)

/-- **Simple-process increment-independence.** For a simple
process `V`, the conditional expectation of its `[0,∞)` integral onto `𝓕_t` is the
`[0,t]` truncation `(V●B)_t`: pick a horizon past `V`'s finite support, where the
`[0,∞)` integral coincides with the truncated process, and apply B1a's martingale
property (`condExp_itoSimple_eq`). -/
lemma condExp_itoIntegralL2_simple (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    μ[(itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V) : Ω → ℝ) | natFiltration hBmeas t]
      =ᵐ[μ] fun ω ↦ itoSimpleProcess hBmeas V t ω := by
  have hbridge : (itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V) : Ω → ℝ)
      =ᵐ[μ] itoSimple hBmeas V := by
    rw [itoIntegralL2_simpleAssembly]
    exact (memLp_itoSimple hB hBmeas V).coeFn_toLp
  exact (condExp_congr_ae hbridge).trans
    (condExp_itoSimple_eq hB (V.value.support.sup (fun p ↦ p.2)) t hBmeas V
      (fun p hp ↦ Finset.le_sup hp))

/-- **The process on a simple integrand is B1a's `[0,t]` discrete integral**:
`(V●B)_t = E[∫₀^∞ V dB | 𝓕_t]` a.e. -/
lemma itoProcessL2Inf_simpleAssembly_ae (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    (itoProcessL2Inf hB t hBmeas (simpleAssembly hBmeas V) : Ω → ℝ)
      =ᵐ[μ] itoSimpleProcess hBmeas V t := by
  rw [itoProcessL2Inf_apply]
  have h := (Lp.memLp (itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V))).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) ((natFiltration hBmeas).le t)
  rw [Lp.toLp_coeFn] at h
  exact h.trans (condExp_itoIntegralL2_simple hB t hBmeas V)

/-- **The unbounded-horizon Itô process starts at zero**, `(f●B)_0 = 0`. On the dense simple
processes this is `itoSimpleProcess_zero_time`, and both sides are continuous-linear in `f`. -/
theorem itoProcessL2Inf_zero_time (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    itoProcessL2Inf hB 0 hBmeas f = 0 := by
  refine congrFun (DenseRange.equalizer (simpleAssembly_denseRange (μ := μ) hBmeas)
    (itoProcessL2Inf hB 0 hBmeas).continuous
    (continuous_const (y := (0 : Lp ℝ 2 μ))) (funext fun V ↦ ?_)) f
  refine Lp.ext ((itoProcessL2Inf_simpleAssembly_ae hB 0 hBmeas V).trans ?_)
  rw [itoSimpleProcess_zero_time]
  exact (Lp.coeFn_zero ℝ 2 μ).symm

end ItoIntegralProcessL2Infinite
end MathFin
