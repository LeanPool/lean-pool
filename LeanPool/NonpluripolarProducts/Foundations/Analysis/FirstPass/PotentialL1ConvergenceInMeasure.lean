/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PotentialL1
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# From canonical L¹ distance to convergence in measure

The canonical extended-real absolute difference controls the ordinary distance
between the `toReal` representatives.  Markov's inequality therefore turns
convergence of its `lintegral` to zero into convergence in measure.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- Passing to `toReal` can only decrease the canonical absolute difference. -/
theorem edist_toReal_le_canonicalERealAbsDiff (a b : EReal) :
    edist a.toReal b.toReal ≤ canonicalERealAbsDiff a b := by
  cases a <;> cases b <;>
    simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff,
      edist_dist, Real.dist_eq, ← EReal.coe_sub, EReal.abs_def]

/-- Almost-everywhere measurable extended-real functions have an
almost-everywhere measurable canonical absolute difference. -/
theorem AEMeasurable.canonicalERealAbsDiff {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {u v : X → EReal}
    (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    AEMeasurable (fun x => canonicalERealAbsDiff (u x) (v x)) μ :=
  measurable_canonicalERealAbsDiff.comp_aemeasurable' (hu.prodMk hv)

/-- Convergence to zero of the canonical extended `L¹` difference implies
convergence in measure of the corresponding real-valued representatives. -/
theorem tendstoInMeasure_toReal_of_lintegral_canonicalERealAbsDiff_tendsto_zero
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ι → X → EReal} {v : X → EReal} {l : Filter ι}
    (hu : ∀ i, AEMeasurable (u i) μ) (hv : AEMeasurable v μ)
    (hL1 : Tendsto
      (fun i => ∫⁻ x, canonicalERealAbsDiff (u i x) (v x) ∂μ)
      l (𝓝 0)) :
    TendstoInMeasure μ (fun i x => (u i x).toReal) l
      (fun x => (v x).toReal) := by
  refine tendstoInMeasure_of_ne_top fun ε hε hε_top => ?_
  have hdiv : Tendsto
      (fun i => (∫⁻ x, canonicalERealAbsDiff (u i x) (v x) ∂μ) / ε)
      l (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const hL1 (Or.inr hε.ne')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
    (fun _ => zero_le) fun i => ?_
  calc
    μ {x | ε ≤ edist (u i x).toReal (v x).toReal} ≤
        μ {x | ε ≤ canonicalERealAbsDiff (u i x) (v x)} := by
      apply measure_mono
      intro x hx
      exact hx.trans (edist_toReal_le_canonicalERealAbsDiff _ _)
    _ ≤ (∫⁻ x, canonicalERealAbsDiff (u i x) (v x) ∂μ) / ε :=
      meas_ge_le_lintegral_div
        (AEMeasurable.canonicalERealAbsDiff (hu i) hv)
        hε.ne' hε_top

/-- A chartwise canonical `L¹` limit gives convergence in measure on the
restricted chart set after taking real representatives. -/
theorem chartL1EDistance_tendstoInMeasure_toReal
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M]
    {ι : Type*} {u : ι → M → EReal} {v : M → EReal} {l : Filter ι}
    (e : ComplexChart n M) (K : Set (ComplexModel n))
    (hu : ∀ i, AEMeasurable (fun z => chartFunction (u i) e z)
      (volume.restrict K))
    (hv : AEMeasurable (fun z => chartFunction v e z)
      (volume.restrict K))
    (hL1 : Tendsto (fun i => chartL1EDistance (u i) v e K) l (𝓝 0)) :
    TendstoInMeasure (volume.restrict K)
      (fun i z => (chartFunction (u i) e z).toReal) l
      (fun z => (chartFunction v e z).toReal) := by
  apply
    tendstoInMeasure_toReal_of_lintegral_canonicalERealAbsDiff_tendsto_zero
      hu hv
  simpa only [chartL1EDistance] using hL1

end

end SGPT.Foundations.Analysis.FirstPass
