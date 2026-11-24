/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PSHD.BallAverage

/-! # Parameter integrals for the Borel measurability lemma

Auxiliary results for Lemma 1.2 of `pshd-vibe`. Measurability is required
only for individual integration sections, never for the joint integrand.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.PSHD

/-- Reverse Fatou preserves upper semicontinuity under a common integrable
majorant. No joint measurability of `f` is assumed. -/
theorem upperSemicontinuous_lintegral_of_dominated
    {X Y : Type*} [TopologicalSpace X] [SequentialSpace X]
    [MeasurableSpace Y] {μ : Measure Y} {f : X → Y → ℝ≥0∞}
    (hmeas : ∀ x, Measurable (f x))
    (husc : ∀ y, UpperSemicontinuous (fun x => f x y))
    (g : Y → ℝ≥0∞) (hbound : ∀ x, f x ≤ᵐ[μ] g)
    (hfinite : ∫⁻ y, g y ∂μ ≠ ⊤) :
    UpperSemicontinuous (fun x => ∫⁻ y, f x y ∂μ) := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  apply isSeqClosed_iff_isClosed.mp
  intro x p hx hp
  have hfatou := limsup_lintegral_le g (fun n => hmeas (x n))
    (fun n => hbound (x n)) hfinite
  have hpoint : ∀ y, limsup (fun n => f (x n) y) atTop ≤ f p y := by
    intro y
    exact (hp.limsup_comp_le_limsup (u := fun z => f z y)).trans
      (upperSemicontinuous_iff_limsup_le.mp (husc y) p)
  change a ≤ ∫⁻ y, f p y ∂μ
  refine le_trans ?_ (hfatou.trans (lintegral_mono hpoint))
  apply le_limsup_of_le (by isBoundedDefault)
  intro b hb
  obtain ⟨n, hn⟩ := hb.exists
  exact (hx n).trans hn

/-- Finite upper truncations have upper semicontinuous section integrals on
a finite measure space, even when the untruncated function is unbounded. -/
theorem upperSemicontinuous_lintegral_min
    {X Y : Type*} [TopologicalSpace X] [SequentialSpace X]
    [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
    {f : X → Y → ℝ≥0∞}
    (hmeas : ∀ x, Measurable (f x))
    (husc : ∀ y, UpperSemicontinuous (fun x => f x y))
    {N : ℝ≥0∞} (hN : N ≠ ⊤) :
    UpperSemicontinuous (fun x => ∫⁻ y, min (f x y) N ∂μ) := by
  apply upperSemicontinuous_lintegral_of_dominated
    (fun x => (hmeas x).min measurable_const)
    (fun y => (husc y).inf upperSemicontinuous_const) (fun _ => N)
  · intro x
    exact Eventually.of_forall (fun y => min_le_right (f x y) N)
  · simpa only [lintegral_const] using
      ENNReal.mul_ne_top hN (measure_ne_top μ univ)

/-- A finite nonnegative integral over a moving ball is continuous whenever
the boundary sphere is null. -/
theorem continuousAt_lintegral_ball
    {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {μ : Measure Y} {f : Y → ℝ≥0∞}
    (hf : Measurable f) (hfinite : ∫⁻ y, f y ∂μ ≠ ⊤)
    {x : Y} {r : ℝ} (hμ : μ (Metric.sphere x r) = 0) :
    ContinuousAt (fun z => ∫⁻ y in Metric.ball z r, f y ∂μ) x := by
  have hi := integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfinite
  have heq : (fun z => ∫⁻ y in Metric.ball z r, f y ∂μ) =
      (fun z => ENNReal.ofReal (∫ y in Metric.ball z r, (f y).toReal ∂μ)) := by
    funext z
    have hz : ∫⁻ y in Metric.ball z r, f y ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite (lintegral_mono' Measure.restrict_le_self le_rfl)
    rw [integral_toReal hf.aemeasurable (ae_lt_top hf hz),
      ENNReal.ofReal_toReal hz]
  rw [heq]
  exact ENNReal.continuous_ofReal.continuousAt.comp
    (continuousAt_integral_ball hi hμ)

/-- Joint measurability of truncated moving-ball integrals follows from
section measurability and upper semicontinuity, without joint measurability
of the original integrand. The finite measure may be a restriction to a
larger disc. -/
theorem measurable_lintegral_ball_min
    {X Y : Type*} [TopologicalSpace X] [SequentialSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} [IsFiniteMeasure μ] {f : X → Y → ℝ≥0∞}
    (hmeas : ∀ x, Measurable (f x))
    (husc : ∀ y, UpperSemicontinuous (fun x => f x y))
    {N : ℝ≥0∞} (hN : N ≠ ⊤) {r : ℝ}
    (hμ : ∀ y, μ (Metric.sphere y r) = 0) :
    Measurable (fun p : X × Y => ∫⁻ y in Metric.ball p.2 r, min (f p.1 y) N ∂μ) := by
  have hc : ∀ x, Continuous (fun z => ∫⁻ y in Metric.ball z r, min (f x y) N ∂μ) := by
    intro x
    apply continuous_iff_continuousAt.mpr
    intro z
    apply continuousAt_lintegral_ball ((hmeas x).min measurable_const) _ (hμ z)
    apply ne_top_of_le_ne_top _ (lintegral_mono (fun y => min_le_right (f x y) N))
    simpa only [lintegral_const] using ENNReal.mul_ne_top hN (measure_ne_top μ univ)
  have hm : ∀ z, Measurable (fun x => ∫⁻ y in Metric.ball z r, min (f x y) N ∂μ) :=
    fun z => (upperSemicontinuous_lintegral_min (μ := μ.restrict (Metric.ball z r))
      hmeas husc hN).measurable
  exact (measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap

end SGPT.Foundations.Analysis.PSHD
