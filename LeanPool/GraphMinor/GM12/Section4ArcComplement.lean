/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.GM11.ForestRegions
import LeanPool.GraphMinor.GM11.Ties
import LeanPool.GraphMinor.GM11.Separate
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# A simple arc does not separate a closed surface

The target-region disc preparation in XII (4.5), page 253,
uses that a proper closed subset of a circle cannot separate
the surface. First prove the corresponding fact for an arc.
Put a one-edge drawing on the arc. It contains no circuit,
since a simple closed curve cannot lie in a line. The forest
complement lemma then proves its complement is connected.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The complement of a simple arc in a connected closed
surface is preconnected. This is used to prove the full
boundary of a non-dense disc region in XII (4.5), page 253. -/
theorem isPreconnected_compl_of_arc {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) : IsPreconnected Lᶜ := by
  classical
  obtain ⟨g, hg, -, hg0, hg1⟩ := hL.exists_arc
  have hab : a ≠ b := by
    intro heq
    have h01 : g 0 = g 1 := hg0.trans (heq.trans hg1.symm)
    exact (show (0 : unitInterval) ≠ 1 by norm_num) (hg.2 h01)
  have hends : ({a, b} : Set S) ⊆ L := by
    rintro z (rfl | rfl)
    · exact hL.left_mem
    · exact hL.right_mem
  obtain ⟨D, hDU, -⟩ := GM11.exists_drawing_on_line 2 hL hab (Set.toFinite ({a, b} : Set S))
    (by simp) (by simp) hends (by rw [ncard_pair hab])
  have hno : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing D → False := by
    intro C hC hCD
    exact GM11.not_isOArc_of_subset_line (GM11.IsLineWithEnds.isLine hL)
      (GM11.IsCircuit.isOArc_U hC) (hCD.U_subset.trans hDU.subset)
  have h := GM11.isPreconnected_compl_of_noCircuit hS D hno
  simpa only [hDU] using h

end GraphMinor.GM12
