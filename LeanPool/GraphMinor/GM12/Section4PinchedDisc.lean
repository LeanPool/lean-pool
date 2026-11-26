/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.PlaneDisc
import LeanPool.GraphMinor.Surface.Wedge
import Mathlib.Analysis.Complex.Norm

/-!
# Thin discs with two fixed ends

The empty discs chosen in XII (4.3), page 250, can be made
thin around a normal arc while keeping its ends fixed. In plane
coordinates, multiply the vertical coordinate of the unit disc by
a continuous width. The width may vanish at the two extreme
horizontal coordinates. It must be positive between them. This
still gives a disc, since those extreme coordinates each have only
one point in the unit disc.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric Complex

/-- Shrinking vertical fibres by a width that is nonzero in the
open horizontal interval preserves injectivity on the closed unit disc. -/
theorem pinched_disc_injOn (ε : ℝ → ℝ)
    (hε : ∀ x ∈ Ioo (-1 : ℝ) 1, ε x ≠ 0) :
    InjOn (fun z : ℂ => (z.re : ℂ) + (ε z.re * z.im : ℝ) * I) (closedBall 0 1) := by
  intro z hz w hw heq
  have hr : z.re = w.re := by
    have h := congrArg Complex.re heq
    simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_self, add_zero] using h
  have hi : ε z.re * z.im = ε w.re * w.im := by
    have h := congrArg Complex.im heq
    simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add] using h
  apply Complex.ext hr
  by_cases hmid : z.re ∈ Ioo (-1 : ℝ) 1
  · rw [← hr] at hi
    exact mul_left_cancel₀ (hε _ hmid) hi
  have hzN : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hwN : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
  have hzR := abs_le.mp ((abs_re_le_norm z).trans hzN)
  have hext : z.re = -1 ∨ z.re = 1 := by
    simp only [mem_Ioo] at hmid
    rcases le_or_gt z.re (-1) with h | h
    · exact Or.inl (le_antisymm h hzR.1)
    · exact Or.inr (le_antisymm hzR.2 (not_lt.mp (fun h' => hmid ⟨h, h'⟩)))
  have habs : |z.re| = 1 := by rcases hext with h | h <;> rw [h] <;> norm_num
  have hz0 : z.im = 0 := abs_re_eq_norm.mp (le_antisymm (abs_re_le_norm z)
    (hzN.trans habs.ge))
  have hw0 : w.im = 0 := abs_re_eq_norm.mp (le_antisymm (abs_re_le_norm w)
    (hwN.trans (by rw [← hr, habs])))
  exact hz0.trans hw0.symm

/-- The thin image remains a closed disc even if its width vanishes
at one or both ends. This is the plane model for the empty discs
in XII (4.3), page 250. -/
theorem isClosedDisc_pinched_disc (ε : ℝ → ℝ) (hc : Continuous ε)
    (hε : ∀ x ∈ Ioo (-1 : ℝ) 1, ε x ≠ 0) :
    IsClosedDisc ((fun z : ℂ => (z.re : ℂ) + (ε z.re * z.im : ℝ) * I) '' closedBall 0 1) := by
  refine (isClosedDisc_image_injOn isClosedDisc_closedBall.1 (isCompact_closedBall _ _)
    ?_ (pinched_disc_injOn ε hε)).1
  exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
      (((Complex.continuous_ofReal.comp ((hc.comp Complex.continuous_re).mul
        Complex.continuous_im))).mul_const I) |>.continuousOn

end GraphMinor.GM12
