/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.RectangleStack
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.RectangleStackDisc
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The disc enclosed by the wall's outer boundary

In each even row the bricks fill the horizontal interval from zero
to `2θ`. In each odd row they fill the interval from one to `2θ-1`.
Stacking those rectangles gives a disc, since consecutive rows
have an overlap of positive length when `θ ≥ 2`. This is the
bounded side of the outer boundary in the rigidity check of
XVI (4.2), page 53.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- The left side of a row of wall bricks. -/
def wallRowLeft (k : ℕ) : ℝ := if Even k then 0 else 1

/-- The right side of a row of wall bricks. -/
def wallRowRight (θ k : ℕ) : ℝ := ((2*θ : ℕ) : ℝ) - wallRowLeft k

/-- The union of the closed brick rows, enclosed by the outer wall boundary. -/
def wallEnclosedSet (θ : ℕ) : Set (ℝ × ℝ) :=
  rectangleStack wallRowLeft (wallRowRight θ) (θ-1)

/-- Every row starts between zero and one. -/
theorem wallRowLeft_bounds (k : ℕ) : 0 ≤ wallRowLeft k ∧ wallRowLeft k ≤ 1 := by
  unfold wallRowLeft
  split_ifs <;> norm_num

/-- The closed brick rows form a disc in the coordinate embedding. -/
theorem isClosedDisc_image_wallEnclosedSet {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {f : (ℝ × ℝ) → S} (hf : IsEmbedding f)
    {θ : ℕ} (hθ : 2 ≤ θ) : IsClosedDisc (f '' wallEnclosedSet θ) := by
  have hθReal : (4 : ℝ) ≤ ((2*θ : ℕ) : ℝ) := by
    exact_mod_cast (show 4 ≤ 2*θ by omega)
  have hWidth (k : ℕ) : wallRowLeft k < wallRowRight θ k := by
    dsimp only [wallRowRight]
    linarith [(wallRowLeft_bounds k).2]
  have hRight (k : ℕ) : ((2*θ : ℕ) : ℝ)-1 ≤ wallRowRight θ k := by
    dsimp only [wallRowRight]
    linarith [(wallRowLeft_bounds k).2]
  have hOverlap (k : ℕ) : max (wallRowLeft k) (wallRowLeft (k+1)) <
      min (wallRowRight θ k) (wallRowRight θ (k+1)) := by
    have hMax : max (wallRowLeft k) (wallRowLeft (k+1)) ≤ 1 :=
      max_le (wallRowLeft_bounds k).2 (wallRowLeft_bounds (k+1)).2
    have hMin : ((2*θ : ℕ) : ℝ)-1 ≤ min (wallRowRight θ k) (wallRowRight θ (k+1)) :=
      le_min (hRight k) (hRight (k+1))
    linarith
  exact isClosedDisc_rectangleStack hS hf wallRowLeft (wallRowRight θ)
    hWidth hOverlap (by omega : 1 ≤ θ-1)

end GraphMinor.GM16
