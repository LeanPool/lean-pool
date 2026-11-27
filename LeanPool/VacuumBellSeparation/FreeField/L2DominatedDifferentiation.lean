/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Dominated limits and complex derivatives in arbitrary actual L2 spaces

Bounds and pointwise limits are checked on specified almost-everywhere
representatives. The Hilbert-space conclusion follows from the genuine
square-integral norm, for any measure, with no finite-measure assumption.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem norm_L2_eq_sqrt_integral_of_ae (f : Lp ℂ 2 μ) (g : α → ℂ)
    (hfg : f =ᵐ[μ] g) : ‖f‖ = Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hsq : ‖f‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem tendsto_L2_zero_of_dominated_representatives
    {β : Type*} {l : Filter β} [l.IsCountablyGenerated]
    (f : β → Lp ℂ 2 μ) (F : β → α → ℂ) (hrep : ∀ i, f i =ᵐ[μ] F i)
    (bound : α → ℝ) (hbound : Integrable bound μ)
    (hdom : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ^ 2 ≤ bound x)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0)) :
    Tendsto f l (𝓝 (0 : Lp ℂ 2 μ)) := by
  have hmeas (i : β) : AEStronglyMeasurable (F i) μ :=
    (Lp.aestronglyMeasurable (f i)).congr (hrep i)
  have ht : Tendsto (fun i => ∫ x, ‖F i x‖ ^ 2 ∂μ) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (F := fun i x => ‖F i x‖ ^ 2) (f := fun _ => (0 : ℝ)) bound
      (Eventually.of_forall fun i => (hmeas i).norm.pow 2)
      (hdom.mono fun i hi => hi.mono fun x hx => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖F i x‖ : ℝ))] using hx)
      hbound (hpoint.mono fun x hx => by simpa using hx.norm.pow 2)
    simpa only [integral_zero] using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he (i : β) : ‖f i‖ = Real.sqrt (∫ x, ‖F i x‖ ^ 2 ∂μ) :=
    norm_L2_eq_sqrt_integral_of_ae μ (f i) (F i) (hrep i)
  simpa only [he, Function.comp_def, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp ht

/-- An actual complex derivative on almost every representative lifts to the
Hilbert space once the squared slope residual has an integrable local bound. -/
theorem hasDerivAt_L2_of_dominated_representatives
    (f : ℂ → Lp ℂ 2 μ) (F : ℂ → α → ℂ) (hrep : ∀ z, f z =ᵐ[μ] F z)
    (g : Lp ℂ 2 μ) (G : α → ℂ) (hgrep : g =ᵐ[μ] G) (z₀ : ℂ)
    (hpoint : ∀ᵐ x ∂μ, HasDerivAt (fun z => F z x) (G x) z₀)
    (bound : α → ℝ) (hbound : Integrable bound μ)
    (hdom : ∀ᶠ z in 𝓝[≠] z₀, ∀ᵐ x ∂μ,
      ‖(z - z₀)⁻¹ • (F z x - F z₀ x) - G x‖ ^ 2 ≤ bound x) :
    HasDerivAt f g z₀ := by
  let q (z : ℂ) : Lp ℂ 2 μ := (z - z₀)⁻¹ • (f z - f z₀) - g
  let Q (z : ℂ) (x : α) : ℂ := (z - z₀)⁻¹ • (F z x - F z₀ x) - G x
  have hqrep (z : ℂ) : q z =ᵐ[μ] Q z := by
    filter_upwards [Lp.coeFn_sub ((z - z₀)⁻¹ • (f z - f z₀)) g,
      Lp.coeFn_smul (z - z₀)⁻¹ (f z - f z₀), Lp.coeFn_sub (f z) (f z₀),
      hrep z, hrep z₀, hgrep] with x hsub hsmul hdiff hz hzero hg
    simp only [q, Q, hsub, hsmul, hdiff, hz, hzero, hg, Pi.smul_apply, Pi.sub_apply]
  have hq : Tendsto q (𝓝[≠] z₀) (𝓝 (0 : Lp ℂ 2 μ)) := by
    apply tendsto_L2_zero_of_dominated_representatives μ q Q hqrep bound hbound hdom
    exact hpoint.mono fun x hx => by
      simpa only [Q, slope, vsub_eq_sub, sub_self] using
        hx.tendsto_slope.sub (tendsto_const_nhds (x := G x))
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  simpa only [q, slope, vsub_eq_sub] using (tendsto_zero_iff_norm_tendsto_zero.mp hq)

end VacuumBellSeparation
