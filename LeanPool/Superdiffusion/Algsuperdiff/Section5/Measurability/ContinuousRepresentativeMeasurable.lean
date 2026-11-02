/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionSelector

/-!
# Measurability of continuous representatives from their averages

Continuity in the spatial variable recovers the value at every interior point
from measurable integrals over shrinking balls.
-/

@[expose] public section



namespace Algsuperdiff.Section5.Measurability

open HCPolySupport MeasureTheory Filter Topology
open Algsuperdiff.Section5.Support

theorem measurable_eval_of_continuousOn_of_setIntegral
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (F : Ω → Vec d → ℝ)
    (hF : ∀ omega, ContinuousOn (F omega) U)
    (hI : ∀ B : Set (Vec d), B ⊆ U →
      Measurable fun omega => ∫ y in B, F omega y ∂volume)
    {x : Vec d} (hx : x ∈ U) : Measurable fun omega => F omega x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
  let r : ℕ → ℝ := fun k => δ * (1 / ((k : ℝ) + 1))
  have hrpos : ∀ k, 0 < r k := fun k => mul_pos hδ (by positivity)
  have hrle : ∀ k, r k ≤ δ := by
    intro k
    apply mul_le_of_le_one_right hδ.le
    apply (div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
    exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hr0 : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto r atTop (𝓝 (δ * 0)))
  have hsub : ∀ k, Metric.ball x (r k) ⊆ U := fun k =>
    (Metric.ball_subset_ball (hrle k)).trans hball
  have hmeas : ∀ k, Measurable fun omega =>
      ⨍ y in Metric.ball x (r k), F omega y ∂volume := by
    intro k
    simp only [setAverage_eq]
    exact (hI _ (hsub k)).const_smul ((volume.real (Metric.ball x (r k)))⁻¹ : ℝ)
  exact measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun omega =>
    tendsto_setAverage_ball_of_continuousOn hU (hF omega) hx hrpos hr0)

end Algsuperdiff.Section5.Measurability
