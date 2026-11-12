/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5064T3Rectangles
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P5098T1OccurrenceSquares]

/-!
# P5098T1OccurrenceSquares

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5098T1OccurrenceSquares (r s : Nat) (o : PeriodicSubtileIndex) :
    let d := match o.label with
      | .A | .B => r
      | .C | .D => s
      | .E | .F => 0
    let c : GaussianInt := match o.label with
      | .A => 0
      | .B => ⟨(s : Int), (s : Int)⟩
      | .C => ⟨(r : Int), 0⟩
      | .D => ⟨0, (r : Int)⟩
      | .E => ⟨(s : Int), (r + s : Nat)⟩
      | .F => ⟨(r : Int), 0⟩
    SubtileOccurrenceInterpretation (P5064T3Rectangles r s)
        ⟨-(r : Int), ((r + s : Nat) : Int)⟩
        ⟨-(s : Int), -((r + s : Nat) : Int)⟩ o =
      TileTranslation (FordTile d)
        (c + ⟨-o.first * r - o.second * s, (r + s) * (o.first - o.second)⟩) := by
-- BODY
  rcases o with ⟨l, m, n⟩
  cases l
  all_goals
    simp? [SubtileOccurrenceInterpretation, P5064T3Rectangles,
      TileTranslation, GaussianTranslation, FordTile, FordCellDomain,
      Finset.image_image]
    try { constructor
          · apply Finset.image_congr
            intro x hx
            apply Zsqrtd.ext <;> simp [Function.comp_def, GaussianTranslation] <;> ring
          · constructor <;> ring }
    try { constructor <;> ring }

end ApollonianSuperharmonic

end
