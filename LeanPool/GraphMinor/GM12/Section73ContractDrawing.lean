/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM12.Section73StarDrawing

public import LeanPool.GraphMinor.GM12.Section73ImageArc
public import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM12.Section4FiniteLineDrawing
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The drawing obtained by contracting one edge

For the radial contractions in XII (7.3), page 261, a contraction
map identifies just one edge closure. Every other edge closure meets
that closure in at most one point, so its image remains a line.
Assemble these image lines into a drawing. Its vertices are precisely
the images of the old vertices, and its edges are precisely the
images of the old edges other than the contracted edge.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A continuous arc contraction gives a drawing with exactly the
expected vertices, edges, and point set when every other edge meets
the contracted arc in at most one point. This constructs the drawings
used in the radial-star contraction of XII (7.3), page 261. -/
theorem exists_drawing_of_edge_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S} {e : Set S}
    (he : e ∈ K.E) {v : S} (hv : v ∈ K.V) (hve : v ∈ closure e)
    (hlines : ∀ g ∈ K.E, ∃ u w : S, IsLineWithEnds (closure g) u w ∧
      closure g ∩ K.V = {u, w})
    (hmeet : ∀ g ∈ K.E, g ≠ e → (closure g ∩ closure e).Subsingleton)
    (f : C(S, S)) (hcollapse : ∀ x ∈ closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ closure e ∧ y ∈ closure e)) :
    ∃ H : Drawing S, H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' (K.E \ {e}) := by
  refine exists_drawing_of_star_collapse (C := {e}) hv hve ?_ ?_ ?_ ?_ f hcollapse hfibre
  · intro g hg
    rw [mem_singleton_iff.mp hg]
  · exact fun g hg => hlines g hg.1
  · exact fun g hg => hmeet g hg.1 hg.2
  · exact fun g hg => closure_inter_subset_V hg.1 he hg.2

end GraphMinor.GM12
