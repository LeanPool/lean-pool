/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SchwartzEvolution
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Dominated real-time differentiation of Schwartz curves in L²

Pointwise scalar derivatives and an actual integrable bound on the squared
slope residual give a derivative of the corresponding L² curve. No topology
on the curve in Schwartz space is assumed. This is useful for real-time wave
evolution, where a complex-time Schwartz power series need not converge.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology
open scoped SchwartzMap ENNReal

/-- The actual L² norm of a Schwartz function, in square-integral form. -/
theorem norm_spatialSchwartz_toL2 (f : SpatialSchwartz) :
    ‖f.toLp 2‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2) := by
  rw [SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), Real.sqrt_eq_rpow]
  norm_num [Real.rpow_two, one_div]

/-- A dominated pointwise limit of actual Schwartz functions converges in L².
The domination is on the squared norm, against an actual integrable function. -/
theorem tendsto_spatialSchwartz_toL2_zero_of_dominated
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (F : α → SpatialSchwartz) (bound : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hbound : Integrable bound)
    (hdom : ∀ᶠ i in l, ∀ᵐ x, ‖F i x‖ ^ 2 ≤ bound x)
    (hpoint : ∀ᵐ x, Tendsto (fun i => F i x) l (𝓝 0)) :
    Tendsto (fun i => (F i).toLp 2) l (𝓝 (0 : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ
      (Fin 3))))) := by
  have ht : Tendsto (fun i => ∫ x, ‖F i x‖ ^ 2) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (F := fun i x => ‖F i x‖ ^ 2) (f := fun _ => (0 : ℝ)) bound
      (Eventually.of_forall fun i => ((F i).continuous.norm.pow 2).aestronglyMeasurable)
      (hdom.mono fun i hi => hi.mono fun x hx => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖F i x‖)] using hx)
      hbound (hpoint.mono fun x hx => by simpa using hx.norm.pow 2)
    simpa only [integral_zero] using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_spatialSchwartz_toL2, Function.comp_def, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp ht

/-- A scalar derivative on every spatial point lifts to a genuine L² derivative
when the squared slope residual has an integrable majorant near the time. -/
theorem hasDerivAt_spatialSchwartz_toL2_of_dominated
    (F : ℝ → SpatialSchwartz) (G : SpatialSchwartz) (t : ℝ)
    (hpoint : ∀ x, HasDerivAt (fun s => F s x) (G x) t)
    (bound : EuclideanSpace ℝ (Fin 3) → ℝ) (hbound : Integrable bound)
    (hdom : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ x,
      ‖(s - t)⁻¹ • (F s x - F t x) - G x‖ ^ 2 ≤ bound x) :
    HasDerivAt (fun s => (F s).toLp 2) (G.toLp 2) t := by
  let Q (s : ℝ) : SpatialSchwartz := (s - t)⁻¹ • (F s - F t) - G
  have hQ : Tendsto (fun s => (Q s).toLp 2) (𝓝[≠] t) (𝓝 (0 : Lp ℂ 2 (volume : Measure
    (EuclideanSpace ℝ (Fin 3))))) := by
    apply tendsto_spatialSchwartz_toL2_zero_of_dominated Q bound hbound
    · simpa only [Q, sub_apply, smul_apply] using hdom
    · exact Eventually.of_forall fun x => by
        simpa only [Q, sub_apply, smul_apply, slope, vsub_eq_sub,
          sub_self] using
          (hpoint x).tendsto_slope.sub (tendsto_const_nhds (x := G x))
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm := (tendsto_zero_iff_norm_tendsto_zero.mp hQ)
  have hQeq (s : ℝ) : (Q s).toLp 2 (μ := volume) =
      slope (fun s => (F s).toLp 2 (μ := volume)) t s - G.toLp 2 (μ := volume) := by
    change SchwartzMap.toLpCLM ℝ ℂ 2 volume (Q s) = _
    simp only [Q, map_sub, map_smul, SchwartzMap.toLpCLM_apply, slope, vsub_eq_sub]
  simpa only [hQeq] using hnorm

end VacuumBellSeparation
