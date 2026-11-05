/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideExitNoFree
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumUnused
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MissingColors

/-!
# Scheide Structural Exits In Base

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideStructuralExitsInBase {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T) :
    ScheideExitVertices T phi ⊆ Finset.univ.image C.y := by
  intro v hv
  have hstructure := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have helementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    hstructure.2.2.2.1
  have hvertex : v ∈ TreeSequenceVertexSet T := by
    let : DecidablePred (fun w : V => ScheideExitVertex T phi w) := Classical.decPred _
    have hexit : ScheideExitVertex T phi v := (Finset.mem_filter.mp hv).2
    rcases hexit with ⟨u, color, defect, hu, hmiss, hdefect, z, path, hpath,
      index, hindex, hvertex, hafter⟩
    exact hvertex
  have base_in_tree : ∀ index : Fin C.p,
      C.y index ∈ TreeSequenceVertexSet T := by
    intro index
    have hlength := C.length_eq
    have witness :=
      (@Finset.mem_image (Fin (T.length + 1)) V (Classical.decEq V)).mpr
        (⟨⟨index.val, by omega⟩, Finset.mem_univ _, C.base_vertex_position index⟩ :
          ∃ a ∈ (Finset.univ : Finset (Fin (T.length + 1))), T.vertex a = C.y index)
    simpa only [TreeSequenceVertexSet] using witness
  obtain ⟨index, hcolor⟩ := C.exit_covered v hv
  obtain ⟨base, hbase⟩ := C.block_color_missing_on_base index
  have hne : v = C.y base := by
    by_contra hne
    have hdisjoint := helementary hvertex (by
      exact base_in_tree base) hne
    exact (Finset.disjoint_left.mp hdisjoint) hcolor hbase
  have witness : v ∈ Finset.univ.image C.y :=
    (@Finset.mem_image (Fin C.p) V (inferInstance : DecidableEq V)).mpr
      ⟨base, Finset.mem_univ _, hne.symm⟩
  exact witness

end GoldbergSeymour

end
