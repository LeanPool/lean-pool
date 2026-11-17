/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The norm potential as a baseline

The Legendre transform of the norm (zero on the closed unit ball, `⊤` outside), its density and
finite positive Haar
mass, and the finite functional value of the norm potential for finite first moment, including
dimension zero.

Supporting infrastructure for Cordero-Erausquin–Klartag, Proposition 12.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section
-- The norm baseline: density and mass of the Legendre transform of the norm.

open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Actual density of the conjugate, including its zero-density exterior. -/
theorem density_legendre_norm :
    density (legendre (fun x : E => (‖x‖ : EReal))) =
      (Metric.closedBall (0 : E) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext y
  by_cases hy : ‖y‖ ≤ 1
  · have hm : y ∈ Metric.closedBall (0 : E) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    simp only [density, legendre_norm, ite_eq_left hy, neg_zero, EReal.exp_zero,
      indicator_of_mem hm]
  · have hm : y ∉ Metric.closedBall (0 : E) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    simp only [density, legendre_norm, ite_eq_right hy, EReal.neg_top, EReal.exp_bot,
      indicator_of_notMem hm]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The baseline exponential mass is the actual positive finite Haar volume of
the closed unit ball, not a supplied mass value or probability normalization. -/
theorem mass_legendre_norm (dx : Measure E) [dx.IsAddHaarMeasure] :
    mass dx (legendre (fun x : E => (‖x‖ : EReal))) = dx (Metric.closedBall 0 1) ∧
      0 < mass dx (legendre (fun x : E => (‖x‖ : EReal))) ∧
      mass dx (legendre (fun x : E => (‖x‖ : EReal))) ≠ ⊤ := by
  have heq : mass dx (legendre (fun x : E => (‖x‖ : EReal))) = dx (Metric.closedBall 0 1) := by
    unfold mass
    rw [density_legendre_norm]
    rw [lintegral_indicator_const measurableSet_closedBall, one_mul]
  rw [heq]
  refine ⟨rfl, ?_, ?_⟩
  · have hpos : 0 < dx (Metric.ball (0 : E) 1) :=
      Measure.measure_pos_of_mem_nhds dx (Metric.ball_mem_nhds 0 zero_lt_one)
    exact hpos.trans_le (measure_mono Metric.ball_subset_closedBall)
  · exact (isCompact_closedBall (0 : E) 1).measure_ne_top
/-- The actual norm potential is admissible and has an actual finite real
functional value whenever the source first moment is finite, including finite
nonprobability measures and dimension zero. -/
theorem norm_baseline_finite (dx μ : Measure E) [dx.IsAddHaarMeasure]
    (hfirst : Integrable (fun x : E => x) μ) :
    ConvexPotential (fun x : E => (‖x‖ : EReal)) ∧
      PotentialIntegrable (fun x : E => (‖x‖ : EReal)) μ ∧
        (∃ L : ℝ, variationalFunctional dx μ (fun x : E => (‖x‖ : EReal)) = (L : EReal)) := by
  have hc : ConvexPotential (fun x : E => (‖x‖ : EReal)) := by
    refine ⟨fun _ => EReal.coe_ne_bot _, ?_⟩
    simpa only [mem_univ, true_and, EReal.coe_le_coe_iff] using
      (convexOn_norm (E := E) convex_univ).convex_epigraph
  have hp : PotentialIntegrable (fun x : E => (‖x‖ : EReal)) μ :=
    ⟨fun _ => EReal.coe_ne_bot _, Eventually.of_forall fun _ => EReal.coe_ne_top _, by
      simpa only [EReal.toReal_coe] using hfirst.norm⟩
  obtain ⟨_heq, hpos, hfin⟩ := mass_legendre_norm dx
  refine
    ⟨hc, hp, Real.log (mass dx (legendre (fun x : E => (‖x‖ : EReal)))).toReal - ∫ x, ‖x‖ ∂μ,
      ?_⟩
  simp only [variationalFunctional, EReal.toReal_coe, ENNReal.log_pos_real hpos.ne' hfin,
    ← EReal.coe_sub]

end

end FunctionalInequalities.Probability.MomentMeasure
