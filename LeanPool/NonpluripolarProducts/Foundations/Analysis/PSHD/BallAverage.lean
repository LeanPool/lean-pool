/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.Indicator

/-! # Continuity of moving-ball integrals

The continuity step in Lemma 1.2 of `pshd-vibe`, separated from
subharmonicity and from joint measurability of the original function.
-/

@[expose] public section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.PSHD

/-- Moving the center of a ball changes the integral continuously at centers
whose boundary sphere is null. -/
theorem continuousAt_integral_ball
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f μ) {x : X} {r : ℝ} (hμ : μ (sphere x r) = 0) :
    ContinuousAt (fun z => ∫ y in ball z r, f y ∂μ) x := by
  have hnot : ∀ᵐ y ∂μ, y ∉ sphere x r := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hμ
  have hlim : ∀ᵐ y ∂μ, ContinuousAt (fun z => (ball z r).indicator f y) x := by
    filter_upwards [hnot] with y hy
    have hxy : x ∉ frontier (ball y r) := by
      intro h
      apply hy
      simpa only [mem_sphere, dist_comm] using frontier_ball_subset_sphere h
    have hc := continuousOn_const.continuousAt_indicator
      (f := fun _ : X => f y) hxy
    have heq : (fun z => (ball z r).indicator f y) =
        (ball y r).indicator (fun _ : X => f y) := by
      funext z
      simp only [Set.indicator, mem_ball, dist_comm]
    rw [heq]
    exact hc
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun y => ‖f y‖)
    (Eventually.of_forall (fun z => hf.aestronglyMeasurable.indicator measurableSet_ball))
    (Eventually.of_forall (fun z => Eventually.of_forall
      (fun y => norm_indicator_le_norm_self (s := ball z r) (f := f) (a := y))))
    hf.norm hlim
  change Tendsto (fun z => ∫ y in ball z r, f y ∂μ) (𝓝 x)
    (𝓝 (∫ y in ball x r, f y ∂μ))
  simpa only [integral_indicator measurableSet_ball] using h

end SGPT.Foundations.Analysis.PSHD
