/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Convexity across a kink

Part of the SVI polynomial-sign certificate (#174).

Two convex pieces whose one-sided derivatives jump upwards at the junction form a convex
function (`convexOn_Ioi_of_convex_pieces`). Used for the zero-scale SVI slice.

## Main results

* `convexOn_Ioi_of_convex_pieces`: if `f` is convex on `(0, J]` and on `[J, ∞)`, and the left
  derivative `dl` at `J` is at most the right derivative `dr`, then `f` is convex on `(0, ∞)`.

## Tags

convexity across a kink, one-sided derivatives, convex pieces, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Set

/-- If two adjacent secant slopes are both at least `L`, so is the joined secant slope. -/
lemma secant_join_lower {f : ℝ → ℝ} {x y z L : ℝ}
    (hxy : x < y) (hyz : y < z)
    (h₁ : L ≤ (f y - f x) / (y - x)) (h₂ : L ≤ (f z - f y) / (z - y)) :
    L ≤ (f z-f x)/(z-x) := by
  rw [le_div_iff₀ (sub_pos.mpr hxy)] at h₁
  rw [le_div_iff₀ (sub_pos.mpr hyz)] at h₂
  rw [le_div_iff₀ (sub_pos.mpr (hxy.trans hyz))]
  nlinarith

/-- If two adjacent secant slopes are both at most `L`, so is the joined secant slope. -/
lemma secant_join_upper {f : ℝ → ℝ} {x y z L : ℝ}
    (hxy : x < y) (hyz : y < z)
    (h₁ : (f y - f x) / (y - x) ≤ L) (h₂ : (f z - f y) / (z - y) ≤ L) :
    (f z-f x)/(z-x) ≤ L := by
  rw [div_le_iff₀ (sub_pos.mpr hxy)] at h₁
  rw [div_le_iff₀ (sub_pos.mpr hyz)] at h₂
  rw [div_le_iff₀ (sub_pos.mpr (hxy.trans hyz))]
  nlinarith

/-- Two convex pieces form a convex function if the derivative jumps upwards
at their shared endpoint. -/
theorem convexOn_Ioi_of_convex_pieces {f : ℝ → ℝ} {J dl dr : ℝ}
    (hJ : 0 < J) (hleft : ConvexOn ℝ (Ioc 0 J) f)
    (hright : ConvexOn ℝ (Ici J) f)
    (hdl : HasDerivWithinAt f dl (Iic J) J)
    (hdr : HasDerivWithinAt f dr (Ici J) J) (hjump : dl ≤ dr) :
    ConvexOn ℝ (Ioi 0) f := by
  have hL {x : ℝ} (hx : 0 < x) (hxJ : x < J) :
      (f J-f x)/(J-x) ≤ dl := by
    simpa only [slope_def_field] using
      hleft.slope_le_of_hasDerivWithinAt_Iio ⟨hx, hxJ.le⟩ ⟨hJ, le_rfl⟩ hxJ
        (hdl.mono Iio_subset_Iic_self)
  have hR {z : ℝ} (hJz : J < z) : dr ≤ (f z-f J)/(z-J) := by
    simpa only [slope_def_field] using
      hright.le_slope_of_hasDerivWithinAt_Ioi (show J ∈ Ici J from mem_Ici.mpr le_rfl)
        hJz.le hJz (hdr.mono Ioi_subset_Ici_self)
  apply convexOn_of_slope_mono_adjacent (convex_Ioi (0 : ℝ))
  intro x y z hx hz hxy hyz
  have hy : 0 < y := lt_trans hx hxy
  by_cases hzJ : z ≤ J
  · exact hleft.slope_mono_adjacent ⟨hx, (hxy.trans hyz).le.trans hzJ⟩ ⟨hz, hzJ⟩ hxy hyz
  by_cases hJx : J ≤ x
  · exact hright.slope_mono_adjacent hJx (hJx.trans (hxy.trans hyz).le) hxy hyz
  have hxJ : x < J := lt_of_not_ge hJx
  have hJz : J < z := lt_of_not_ge hzJ
  rcases lt_trichotomy y J with hyJ | rfl | hJy
  · have hxyJ := hleft.slope_mono_adjacent ⟨hx, hxJ.le⟩ ⟨hJ, le_rfl⟩ hxy hyJ
    exact secant_join_lower hyJ hJz hxyJ
      (hxyJ.trans ((hL hy hyJ).trans (hjump.trans (hR hJz))))
  · exact (hL hx hxJ).trans (hjump.trans (hR hJz))
  · have hJyz := hright.slope_mono_adjacent (show J ∈ Ici J from mem_Ici.mpr le_rfl) hJz.le hJy hyz
    exact secant_join_upper hxJ hJy
      (((hL hx hxJ).trans (hjump.trans (hR hJy))).trans hJyz) hJyz

end SVI
end MathFin
