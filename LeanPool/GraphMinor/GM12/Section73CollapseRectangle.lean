/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CollapseInterval
public import LeanPool.GraphMinor.Surface.ArcDisc
import Mathlib.Analysis.Complex.ReImTopology

/-!
# A rectangle map collapsing its central axis interval

For the radial contractions in XII (7.3), page 261, interpolate the
interval collapse with the identity on each horizontal line of a
rectangle. The interpolation reaches the collapse only on its axis.
The boundary stays fixed, and every horizontal interval maps onto
itself. This permits the map to be pasted into a surface strip.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology Complex

/-- The rectangle supporting a collapse of the axis interval `[l,r]`. -/
def collapseRectangle (l r ε : ℝ) : Set ℂ :=
  Icc (2 * l - r) (2 * r - l) ×ℂ Icc (-ε) ε

/-- The collapse weight is one on the axis and zero on the horizontal
boundary of the rectangle. -/
noncomputable def collapseWeight (ε : ℝ) (z : ℂ) : ℝ := 1 - |z.im| / ε

/-- The rectangle coordinate map used to contract a drawn edge. -/
noncomputable def collapseStrip (l r ε : ℝ) (z : ℂ) : ℂ :=
  (((1 - collapseWeight ε z) * z.re + collapseWeight ε z * collapseInterval l r z.re : ℝ) : ℂ) +
    z.im * I

/-- The rectangle map is continuous. -/
theorem continuous_collapseStrip (l r ε : ℝ) : Continuous (collapseStrip l r ε) := by
  have hψ := continuous_collapseInterval l r
  unfold collapseStrip collapseWeight
  fun_prop

/-- The map keeps the vertical coordinate. -/
theorem collapseStrip_im (l r ε : ℝ) (z : ℂ) : (collapseStrip l r ε z).im = z.im := by
  simp [collapseStrip]

/-- Its horizontal coordinate is the interpolated interval collapse. -/
theorem collapseStrip_re (l r ε : ℝ) (z : ℂ) :
    (collapseStrip l r ε z).re =
      (1 - collapseWeight ε z) * z.re + collapseWeight ε z * collapseInterval l r z.re := by
  simp [collapseStrip]

/-- The weight lies between zero and one throughout the rectangle. -/
theorem collapseWeight_mem {l r ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z ∈ collapseRectangle l r ε) : collapseWeight ε z ∈ Icc (0 : ℝ) 1 := by
  have him : |z.im| ≤ ε := abs_le.mpr hz.2
  constructor
  · exact sub_nonneg.mpr ((div_le_one hε).mpr him)
  · exact sub_le_self _ (div_nonneg (abs_nonneg _) hε.le)

/-- The rectangle maps into itself. -/
theorem collapseStrip_mapsTo {l r ε : ℝ} (hlr : l ≤ r) (hε : 0 < ε) :
    MapsTo (collapseStrip l r ε) (collapseRectangle l r ε) (collapseRectangle l r ε) := by
  intro z hz
  have hs := collapseWeight_mem hε hz
  have hmono := collapseInterval_interpolation_monotone (l := l) (r := r) hs.1 hs.2
  obtain ⟨hleft, hright⟩ := collapseInterval_interpolation_endpoints (t := collapseWeight ε z) hlr
  refine ⟨?_, ?_⟩
  · change (collapseStrip l r ε z).re ∈ Icc _ _
    rw [collapseStrip_re]
    exact ⟨hleft ▸ hmono hz.1.1, hright ▸ hmono hz.1.2⟩
  · change (collapseStrip l r ε z).im ∈ Icc _ _
    rw [collapseStrip_im]
    exact hz.2

/-- On the axis, the rectangle map is the interval collapse. -/
theorem collapseStrip_ofReal (l r ε x : ℝ) :
    collapseStrip l r ε (x : ℂ) = (collapseInterval l r x : ℂ) := by
  simp [collapseStrip, collapseWeight]

/-- The rectangle boundary stays fixed. -/
theorem collapseStrip_frontier {l r ε : ℝ} (hlr : l ≤ r) (hε : 0 < ε)
    {z : ℂ} (hz : z ∈ frontier (collapseRectangle l r ε)) : collapseStrip l r ε z = z := by
  have hRc : IsCompact (collapseRectangle l r ε) := isCompact_Icc.reProdIm isCompact_Icc
  rw [hRc.isClosed.frontier_eq, collapseRectangle, interior_reProdIm, interior_Icc,
    interior_Icc] at hz
  obtain ⟨hzR, hznot⟩ := hz
  apply Complex.ext
  · rw [collapseStrip_re]
    obtain ⟨hleft, hright⟩ := collapseInterval_interpolation_endpoints (t := collapseWeight ε z) hlr
    by_cases hzl : z.re = 2 * l - r
    · simpa only [hzl] using hleft
    by_cases hzr : z.re = 2 * r - l
    · simpa only [hzr] using hright
    have himnot : z.im ∉ Ioo (-ε) ε := fun him => hznot
      ⟨⟨lt_of_le_of_ne hzR.1.1 (Ne.symm hzl), lt_of_le_of_ne hzR.1.2 hzr⟩, him⟩
    have him : |z.im| = ε := by
      apply le_antisymm (abs_le.mpr hzR.2)
      by_contra hn
      exact himnot (abs_lt.mp (lt_of_not_ge hn))
    have hs : collapseWeight ε z = 0 := by
      unfold collapseWeight
      rw [him, div_self hε.ne']
      exact sub_self _
    rw [hs]
    ring
  · exact collapseStrip_im l r ε z

/-- Only the axis attains full collapse weight. -/
theorem collapseWeight_lt_one {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : z.im ≠ 0) :
    collapseWeight ε z < 1 := by
  have hpos : 0 < |z.im| / ε := div_pos (abs_pos.mpr hz) hε
  unfold collapseWeight
  linarith

/-- The central axis interval is the only non-singleton fibre of
the rectangle map. Away from the axis, the interpolation is strictly
increasing on its horizontal line. -/
theorem collapseStrip_eq_iff {l r ε : ℝ} (hlr : l ≤ r) (hε : 0 < ε) {z w : ℂ}
    (hz : z ∈ collapseRectangle l r ε) :
    collapseStrip l r ε z = collapseStrip l r ε w ↔
      z = w ∨ (z ∈ Complex.ofReal '' Icc l r ∧ w ∈ Complex.ofReal '' Icc l r) := by
  constructor
  · intro heq
    have him : z.im = w.im := by
      have him := congrArg Complex.im heq
      simpa only [collapseStrip_im] using him
    have hs : collapseWeight ε z = collapseWeight ε w := by simp only [collapseWeight, him]
    have hre := congrArg Complex.re heq
    rw [collapseStrip_re, collapseStrip_re, ← hs] at hre
    by_cases hz0 : z.im = 0
    · have hw0 : w.im = 0 := him.symm.trans hz0
      have hs1 : collapseWeight ε z = 1 := by simp [collapseWeight, hz0]
      rw [hs1] at hre
      simp only [sub_self, zero_mul, one_mul, zero_add] at hre
      rcases (collapseInterval_eq_iff hlr).mp hre with hre | ⟨hzr, hwr⟩
      · exact Or.inl (Complex.ext hre him)
      · exact Or.inr ⟨⟨z.re, hzr, Complex.ext rfl (by simp [hz0])⟩,
          ⟨w.re, hwr, Complex.ext rfl (by simp [hw0])⟩⟩
    · have hstrict := collapseInterval_interpolation_strictMono
        (l := l) (r := r) (collapseWeight_mem hε hz).1 (collapseWeight_lt_one hε hz0)
      exact Or.inl (Complex.ext (hstrict.injective hre) him)
  · rintro (rfl | ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩)
    · rfl
    · rw [collapseStrip_ofReal, collapseStrip_ofReal, collapseInterval_of_mem hx,
        collapseInterval_of_mem hy]

end GraphMinor.GM12
