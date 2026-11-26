/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Closed subintervals of an edge arc

The subdivision step in XII (4.5), page 252, takes the portions
of an arc between successive cuts. The affine parametrization
`pieceA` gives each portion as a simple arc. Injectivity of the
original parametrization says exactly which original parameters
belong to each portion.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- Membership in an arc portion is exactly membership of the
original parameter in the corresponding closed interval. This
transfers the one-crossing interval calculation in XII (4.5), page 252. -/
theorem mem_range_pieceA_iff {S : Type u}
    {g : unitInterval → S} (hg : Function.Injective g)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (t : unitInterval) :
    g t ∈ range (pieceA g a b) ↔ (t : ℝ) ∈ Icc a b := by
  rw [range_pieceA g ha hab hb]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hq01 : q ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hq.1, hq.2.trans hb⟩
    have hqt : q = (t : ℝ) := extI_injOn hg hq01 t.property
      (heq.trans (extI_coe g t).symm)
    simpa only [hqt] using hq
  · intro ht
    exact ⟨t, ht, extI_coe g t⟩

/-- Every portion of an arc lies on the original arc. -/
theorem range_pieceA_subset_range {S : Type u}
    (g : unitInterval → S) (a b : ℝ) : range (pieceA g a b) ⊆ range g := by
  rintro x ⟨t, rfl⟩
  exact ⟨_, rfl⟩

/-- A nondegenerate portion of a simple arc is a line with the
selected cut points as ends, as needed in XII (4.5), page 252. -/
theorem isLineWithEnds_pieceA {S : Type u} [TopologicalSpace S] [T2Space S]
    {g : unitInterval → S} (hg : IsArcMap g)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    IsLineWithEnds (range (pieceA g a b)) (extI g a) (extI g b) := by
  have h := (isArcMap_pieceA hg ha hab hb).isLineWithEnds
  simpa only [pieceA_zero, pieceA_one] using h

end GraphMinor.GM12
