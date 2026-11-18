/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Norm
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Temperate functions in L1 and L2 under exponential moments

The source has its Borel structure and the target is an arbitrary real normed
space. For L1, either space is second countable; real targets need no such source
hypothesis. The L2 result retains its second-countable source. No Hilbert,
finite-dimensional or probability normalization hypothesis is needed.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FunctionalInequalities.Probability

section TemperateIntegrability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

omit [SecondCountableTopology E] in
/-- Temperate functions are integrable under all norm exponential moments.
The target is any real normed space; no completeness or probability normalization is assumed. -/
theorem integrable_of_hasTemperateGrowth {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [SecondCountableTopologyEither E F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
    (hg : g.HasTemperateGrowth) : Integrable g μ := by
  obtain ⟨k, C, hb⟩ := hg.2 0
  exact integrable_of_norm_le_pow μ hexp hg.1.continuous.aestronglyMeasurable
    (fun x => by simpa only [norm_iteratedFDeriv_zero] using hb x)

/-- Temperate functions belong to L2 under all norm exponential moments. -/
theorem memLp_two_of_hasTemperateGrowth {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → H}
    (hf : f.HasTemperateGrowth) : MemLp f 2 μ := by
  obtain ⟨k, C, hb⟩ := hf.2 0
  have hb' : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k := fun x => by
    simpa only [norm_iteratedFDeriv_zero] using hb x
  refine (memLp_two_iff_integrable_sq_norm hf.1.continuous.aestronglyMeasurable).2 ?_
  refine integrable_of_norm_le_pow μ hexp (hf.1.continuous.aestronglyMeasurable.norm.pow 2)
    (C := C ^ 2) (k := 2 * k) (fun x => ?_)
  have h0 : 0 ≤ ‖f x‖ := norm_nonneg _
  have hsq : ‖f x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := pow_le_pow_left₀ h0 (hb' x) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖f x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := hsq
    _ = C ^ 2 * (1 + ‖x‖) ^ (2 * k) := by ring


end TemperateIntegrability

end FunctionalInequalities.Probability
