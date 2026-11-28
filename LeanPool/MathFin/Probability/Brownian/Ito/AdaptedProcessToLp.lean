/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense

/-!
# Realizing a bounded adapted continuous process as an Itô-integrand class (the σ-realization)

The Itô integral `∫₀ᵀ σ dB` (`ItoIntegralCLM.itoIntegralCLM`) takes its integrand from the
**predictable** `L²` space `E := Lp ℝ 2 (trimMeasure T)` — an `Lp` class over the trim product
measure on the predictable σ-algebra, never a raw process `σ : ℝ≥0 → Ω → ℝ`. To integrate a genuine
bounded adapted process (e.g. a continuous market price of risk `θ` for the general adapted Girsanov
theorem), one must first **realize** it inside `E`. This is the σ-realization: the last piece of
"the concrete adapted stochastic integral" (SP0, half (i)) that the drift/Itô SDE files build only
for their specific processes.

For an **every-`ω`-continuous** bounded adapted `σ` this is a short assembly on the existing tower —
no a.e./everywhere friction, exactly as `DriftProcessPredictable.driftSimpleProcess` handles its
elementary drift:

* `MathFin.isStronglyPredictable_of_bdd_adapted_cont` — continuous + adapted ⟹ predictable, via
  Degenne's `StronglyAdapted.isStronglyPredictable_of_leftContinuous` (continuity gives the
  left-continuity it wants);
* `MathFin.memLp_uncurry_of_bdd_adapted_cont` — predictable + bounded on the *finite* measure
  `trimMeasure T` ⟹ `MemLp … 2`;
* `MathFin.processToLp` — the realization `σ ↦ (its class in E)`, with `processToLp_coeFn` the a.e.
  identification back to `Function.uncurry σ`.

This unblocks the continuous-adapted Girsanov (brick α4): `∫θdB` and its Doléans density are now
formable for a bounded adapted continuous `θ`.

## Main definitions

* `processToLp`: the realization of a bounded adapted process with continuous paths as an
  element of the Itô-integrand space `Lp ℝ 2 (trimMeasure T)`.
* `processToLpPredictable`: the same realization for a bounded strongly predictable process.

## Main results

* `isStronglyPredictable_of_bdd_adapted_cont`: a bounded adapted process with continuous paths
  is strongly predictable.
* `isStronglyPredictable_deterministic`, `isStronglyPredictable_const`,
  `isStronglyPredictable_time`: a continuous function of time alone, a constant, and time itself
  are predictable.
* `isStronglyPredictable_comp_path`: a Borel function of time and a continuous adapted path is
  predictable.
* `memLp_uncurry_of_bdd_adapted_cont`, `memLp_uncurry_of_bdd_predictable`: such a process, and
  any bounded predictable one, is in `L²` over `trimMeasure T`.
* `processToLp_coeFn`, `processToLpPredictable_coeFn`: the realization agrees with the process
  `trimMeasure T`-almost everywhere.
* `processToLpPredictable_ae_slice`: the predictable realization agrees with the process on almost
  every `ω`-slice.

## Tags

Itô integrand, predictable process, stochastic integral, market price of risk, L2 space, MSC 60H05,
MSC 60G07
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin

open ItoIntegralL2 ItoIntegralCLM

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **A bounded adapted continuous process is predictable.** For an `𝓕`-adapted `σ` that is
continuous in time for every `ω`, the space-time function `(t, ω) ↦ σ t ω` is measurable for the
predictable σ-algebra — continuity gives the left-continuity Degenne's
`StronglyAdapted.isStronglyPredictable_of_leftContinuous` requires, and no randomness in the
time-regularity means no exceptional null set to dodge. -/
theorem isStronglyPredictable_of_bdd_adapted_cont (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) :
    IsStronglyPredictable (natFiltration hBmeas) σ := by
  apply MeasureTheory.StronglyAdapted.isStronglyPredictable_of_leftContinuous hadap
  exact fun ω a ↦ (hcont ω).continuousWithinAt

/-- **A deterministic continuous function of time is predictable** for the natural filtration. -/
theorem isStronglyPredictable_deterministic (hBmeas : ∀ t, Measurable (B t)) {f : ℝ≥0 → ℝ}
    (hf : Continuous f) :
    IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) (_ : Ω) ↦ f s :=
  isStronglyPredictable_of_bdd_adapted_cont hBmeas (fun _ ↦ stronglyMeasurable_const)
    fun _ ↦ hf

/-- A constant process is predictable for the natural filtration. -/
theorem isStronglyPredictable_const (hBmeas : ∀ t, Measurable (B t)) (c : ℝ) :
    IsStronglyPredictable (natFiltration hBmeas) fun (_ : ℝ≥0) (_ : Ω) ↦ c :=
  isStronglyPredictable_deterministic hBmeas continuous_const

/-- Time itself, `(s, ω) ↦ s`, is predictable for the natural filtration. -/
theorem isStronglyPredictable_time (hBmeas : ∀ t, Measurable (B t)) :
    IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) (_ : Ω) ↦ (s : ℝ) :=
  isStronglyPredictable_deterministic hBmeas NNReal.continuous_coe

/-- **A Borel function of time and a continuous adapted path is predictable.** -/
theorem isStronglyPredictable_comp_path (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {h : ℝ → ℝ → ℝ}
    (hh : Measurable fun p : ℝ × ℝ ↦ h p.1 p.2) :
    IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) ω ↦ h s (B s ω) :=
  (hh.comp (StronglyMeasurable.prodMk (isStronglyPredictable_time hBmeas)
    (isStronglyPredictable_of_bdd_adapted_cont hBmeas (stronglyAdapted_natFiltration hBmeas)
      hBcont)).measurable).stronglyMeasurable

/-- **A bounded adapted continuous process is `L²` over `trimMeasure T`.** It is predictable
(`isStronglyPredictable_of_bdd_adapted_cont`) and bounded, and `trimMeasure T` is a finite
measure, so `MemLp.of_bound` applies. -/
theorem memLp_uncurry_of_bdd_adapted_cont (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    MemLp (Function.uncurry σ) 2 (trimMeasure (μ := μ) T hBmeas) :=
  MemLp.of_bound
    (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont).aestronglyMeasurable
    C (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hbdd z.1 z.2)

/-- **The σ-realization.** A bounded adapted continuous process realized as an element of the
Itô-integrand space `E = Lp ℝ 2 (trimMeasure T)` — the domain of
`ItoIntegralCLM.itoIntegralCLM`. This is the missing bridge from a raw bounded adapted continuous
process `σ : ℝ≥0 → Ω → ℝ` to `∫₀ᵀ σ dB`; with it, the general continuous-adapted Girsanov density is
formable. -/
noncomputable def processToLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  (memLp_uncurry_of_bdd_adapted_cont T hBmeas hadap hcont hbdd).toLp (Function.uncurry σ)

/-- **The realization agrees with `σ` a.e.**
`processToLp T σ =ᵐ[trimMeasure T] Function.uncurry σ` — the identification that lets Itô-integral
computations read the class back as the process. -/
theorem processToLp_coeFn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    processToLp (μ := μ) T hBmeas hadap hcont hbdd
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry σ :=
  (memLp_uncurry_of_bdd_adapted_cont T hBmeas hadap hcont hbdd).coeFn_toLp

/-! ### The σ-realization for a bounded **predictable** integrand (Girsanov Rung 1)

Dropping the continuity hypothesis: the Itô integral's domain is the *predictable* `L²` space, so a
bounded process that is already strongly predictable needs no continuity to be realized — the
`aestronglyMeasurable` it carries is exactly what `MemLp.of_bound` consumes. The continuous
realization above is the special case `IsStronglyPredictable` =
`isStronglyPredictable_of_bdd_adapted_cont`. -/

/-- **A bounded predictable process is `L²` over `trimMeasure T`.** Predictable + bounded on the
finite measure `trimMeasure T` ⟹ `MemLp.of_bound`; the continuity of
`memLp_uncurry_of_bdd_adapted_cont` is dropped. -/
theorem memLp_uncurry_of_bdd_predictable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) σ)
    {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    MemLp (Function.uncurry σ) 2 (trimMeasure (μ := μ) T hBmeas) :=
  MemLp.of_bound hpred.aestronglyMeasurable C
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hbdd z.1 z.2)

/-- **The σ-realization for a bounded predictable process.** Realizes a bounded strongly-predictable
`σ : ℝ≥0 → Ω → ℝ` as an element of the Itô-integrand space `E = Lp ℝ 2 (trimMeasure T)` — the
domain of `ItoIntegralCLM.itoIntegralCLM` — with no continuity assumption. -/
noncomputable def processToLpPredictable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) σ)
    {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  (memLp_uncurry_of_bdd_predictable T hBmeas hpred hbdd).toLp (Function.uncurry σ)

/-- **The predictable realization agrees with `σ` a.e.** -/
theorem processToLpPredictable_coeFn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) σ)
    {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    processToLpPredictable (μ := μ) T hBmeas hpred hbdd
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry σ :=
  (memLp_uncurry_of_bdd_predictable T hBmeas hpred hbdd).coeFn_toLp

/-- **The predictable realization agrees with `σ` on almost every `ω`-slice.** The a.e.
identification `processToLpPredictable_coeFn` over `trimMeasure`, read through the product measure
`timeMeasureHorizon T ⊗ μ` (`ae_eq_of_ae_eq_trim`) as: for `μ`-a.e. `ω`, the path `s ↦ σ s ω` and
the representative `s ↦ ⇑(processToLpPredictable σ) (s, ω)` agree for `timeMeasureHorizon T`-a.e.
`s`. -/
theorem processToLpPredictable_ae_slice (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) σ)
    {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    ∀ᵐ ω ∂μ, ∀ᵐ s ∂(timeMeasureHorizon T),
      processToLpPredictable (μ := μ) T hBmeas hpred hbdd (s, ω) = σ s ω :=
  Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := timeMeasureHorizon T)).quasiMeasurePreserving.ae
      (ae_eq_of_ae_eq_trim (processToLpPredictable_coeFn (μ := μ) T hBmeas hpred hbdd)))

end MathFin
