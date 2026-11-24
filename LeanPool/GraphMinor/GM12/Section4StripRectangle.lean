/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ArcDisc
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A rectangle around a compact straight arc

For XII (4.3), claim (7), page 251, motions along arcs must have
support in an assigned open set. A compact real interval in an open
plane set has a thin rectangular neighborhood in that set. The
rectangle extends beyond both ends, so a strip slide can move one
end to the other.
-/

public section

namespace GraphMinor.GM12

open Set Metric Complex

/-- A compact straight arc has a rectangular neighborhood extending
past both ends inside any prescribed open neighborhood. -/
theorem exists_strip_rectangle {O : Set ℂ} (hO : IsOpen O)
    {x y : ℝ} (hxy : x ≤ y) (hseg : Complex.ofReal '' Icc x y ⊆ O) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (x - δ) (y + δ) ×ℂ Icc (-δ) δ ⊆ O := by
  obtain ⟨ρ, hρ, htube⟩ :=
    (isCompact_Icc.image Complex.continuous_ofReal).exists_thickening_subset_open hO hseg
  let δ := ρ / 4
  have hδ : 0 < δ := div_pos hρ (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  let r := max x (min y z.re)
  have hr : r ∈ Icc x y :=
    ⟨le_max_left _ _, max_le hxy (min_le_left _ _)⟩
  have hzr : |z.re - r| ≤ δ := by
    rw [abs_le]
    constructor
    · have hrle : r ≤ z.re + δ := by
        apply max_le
        · linarith [hz.1.1]
        · exact (min_le_right _ _).trans (le_add_of_nonneg_right hδ.le)
      linarith
    · have hrge : z.re - δ ≤ r := by
        apply le_trans _ (le_max_right _ _)
        apply le_min
        · linarith [hz.1.2]
        · exact sub_le_self _ hδ.le
      linarith
  apply htube
  apply mem_thickening_iff.mpr
  refine ⟨(r : ℂ), ⟨r, hr, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have hn := norm_le_abs_re_add_abs_im (z - (r : ℂ))
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hn
  have him : |z.im| ≤ δ := abs_le.mpr hz.2
  have htwo : 2 * δ < ρ := by dsimp only [δ]; linarith
  exact lt_of_le_of_lt (hn.trans (add_le_add hzr him)) (by linarith)

end GraphMinor.GM12
