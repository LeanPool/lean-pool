/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Convex.Slope

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Restoring the zero parameter in chord comparisons

A chord comparison valid at all nonzero triples extends through a single
interior point by continuity there. No continuity of the function at the
other endpoints, including a finite moment-domain boundary, is required.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace EhrhardGaussian.GaussianConvexity

/-- The barycentric chord inequality is equivalent to the adjacent-secant inequality. -/
theorem adjacent_slope_le_of_chord {f : ℝ → ℝ} {x y z : ℝ} (hxy : x < y) (hyz : y < z)
    (h : f y ≤ ((z - y) * f x + (y - x) * f z) / (z - x)) :
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) := by
  have h' := (le_div_iff₀ (sub_pos.mpr (hxy.trans hyz))).mp h
  apply (div_le_div_iff₀ (sub_pos.mpr hxy) (sub_pos.mpr hyz)).mpr
  nlinarith only [h']

/-- Convexity extends across zero from nonzero chord triples and continuity at zero. -/
theorem convexOn_of_nonzero_chords {s : Set ℝ} {f : ℝ → ℝ} (hs : Convex ℝ s)
    (h0 : 0 ∈ interior s) (hf : ContinuousAt f 0)
    (hchord : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
      x ≠ 0 → y ≠ 0 → z ≠ 0 →
      f y ≤ ((z - y) * f x + (y - x) * f z) / (z - x)) :
    ConvexOn ℝ s f := by
  have hslope : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
      x ≠ 0 → y ≠ 0 → z ≠ 0 →
      (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
    fun hx hz hxy hyz hx0 hy0 hz0 => adjacent_slope_le_of_chord hxy hyz
      (hchord hx hz hxy hyz hx0 hy0 hz0)
  have hS : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ s :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ s from mem_interior_iff_mem_nhds.mp h0).filter_mono
      nhdsWithin_le_nhds
  apply convexOn_of_slope_mono_adjacent hs
  intro x y z hx hz hxy hyz
  by_cases hx0 : x = 0
  · subst x
    have hL : Tendsto (fun t => (f y - f t) / (y - t)) (𝓝[≠] 0)
        (𝓝 ((f y - f 0) / (y - 0))) :=
      ((continuousAt_const.sub hf).div (continuousAt_const.sub continuousAt_id)
        (sub_ne_zero.mpr hxy.ne')).tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hL
    filter_upwards [hS, (eventually_lt_nhds hxy).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t htS hty ht0
    exact hslope htS hz hty hyz ht0 hxy.ne' (hxy.trans hyz).ne'
  by_cases hy0 : y = 0
  · subst y
    have hL : Tendsto (fun t => (f t - f x) / (t - x)) (𝓝[≠] 0)
        (𝓝 ((f 0 - f x) / (0 - x))) :=
      ((hf.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hxy.ne')).tendsto.mono_left nhdsWithin_le_nhds
    have hR : Tendsto (fun t => (f z - f t) / (z - t)) (𝓝[≠] 0)
        (𝓝 ((f z - f 0) / (z - 0))) :=
      ((continuousAt_const.sub hf).div (continuousAt_const.sub continuousAt_id)
        (sub_ne_zero.mpr hyz.ne')).tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hL hR
    filter_upwards [(eventually_gt_nhds hxy).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hyz).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hxt htz ht0
    exact hslope hx hz hxt htz hx0 ht0 hyz.ne'
  by_cases hz0 : z = 0
  · subst z
    have hR : Tendsto (fun t => (f t - f y) / (t - y)) (𝓝[≠] 0)
        (𝓝 ((f 0 - f y) / (0 - y))) :=
      ((hf.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hyz.ne')).tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hR
    filter_upwards [hS, (eventually_gt_nhds hyz).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t htS hyt ht0
    exact hslope hx htS hxy hyt hx0 hy0 ht0
  exact hslope hx hz hxy hyz hx0 hy0 hz0

end EhrhardGaussian.GaussianConvexity
