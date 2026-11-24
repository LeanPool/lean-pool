/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.RectangleStack
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.RectangleStackStep
import LeanPool.GraphMinor.GM16.RectangularDisc
import Mathlib.Tactic.Linarith

/-!
# A stack of overlapping rows is a disc

Start with the bottom rectangle. A new row meets the preceding
stack in the overlap of their horizontal sides. Positive overlap
makes that side a line, and the rectangle append lemma proves that
the union is still a disc. This constructs the enclosed disc for
the outer face of the wall in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- Nondegenerate rows whose consecutive horizontal intervals overlap
in positive length form a disc, after embedding in a closed surface. -/
theorem isClosedDisc_rectangleStack {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {f : (ℝ × ℝ) → S} (hf : IsEmbedding f)
    (left right : ℕ → ℝ) (hWidth : ∀ k, left k < right k)
    (hOverlap : ∀ k, max (left k) (left (k + 1)) < min (right k) (right (k + 1)))
    {n : ℕ} (hn : 1 ≤ n) : IsClosedDisc (f '' rectangleStack left right n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      have hRect := isClosedDisc_image_real_rectangle hf (hWidth 0)
        (show (0 : ℝ) < 0+1 by norm_num)
      simpa [rectangleStack] using hRect
    have hn1 : 1 ≤ n := by omega
    have hPrev : n-1+1 = n := by omega
    have hPos : max (left (n-1)) (left n) < min (right (n-1)) (right n) := by
      simpa only [hPrev] using hOverlap (n-1)
    rw [rectangleStack_succ]
    exact isClosedDisc_append_rectangle hS hf (ih hn1) (hWidth n)
      (show (n : ℝ) < (n : ℝ)+1 by linarith) hPos
      (fun _ hp => rectangleStack_vertical_le hp) (rectangleStack_inter_next hn1)

end GraphMinor.GM16
