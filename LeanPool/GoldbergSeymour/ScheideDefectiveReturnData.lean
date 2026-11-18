/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup

/-!
# Scheide Defective Return Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- The final departure of a replacement defective chain, with its boundary edge and block-color
witnesses.
-/
structure ScheideDefectiveReturnData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) }) where
  /-- The position of the last inside vertex on the defective chain. -/
  pathIndex : Fin ((D.replacementPath d).length + 1)
  /-- The position of the boundary edge immediately following that vertex. -/
  edgeIndex : Fin ((D.replacementPath d).length + 1)
  /-- The position of the following outside vertex. -/
  outsideIndex : Fin ((D.replacementPath d).length + 1)
  /-- The first selected vertex inside the tree. -/
  v1 : V
  /-- The first selected boundary edge. -/
  f1 : E
  /-- The first selected outside vertex. -/
  u1 : V
  /-- The structural block whose color is missing at the selected vertex. -/
  blockIndex : Fin C.s
  v1_at_index : (D.replacementPath d).getVert pathIndex.val = Sum.inl v1
  f1_at_index : (D.replacementPath d).getVert edgeIndex.val = Sum.inr f1
  u1_at_index : (D.replacementPath d).getVert outsideIndex.val = Sum.inl u1
  successive_indices : edgeIndex.val = pathIndex.val + 1 ∧ outsideIndex.val = pathIndex.val + 2
  after_last_tree_vertex :
    ∀ r : Fin ((D.replacementPath d).length + 1),
      pathIndex.val < r.val →
        ∀ x : V, (D.replacementPath d).getVert r.val = Sum.inl x → x ∉ TreeSequenceVertexSet T
  v1_mem : v1 ∈ TreeSequenceVertexSet T
  v1_ne_v0 : v1 ≠ D.v0 d
  u1_outside : u1 ∉ TreeSequenceVertexSet T
  v1_is_exit : v1 ∈ ScheideExitVertices T phi
  v1_in_base : v1 ∈ Finset.univ.image C.y
  f1_color : phi f1 = some d.1
  f1_ends : G.ends f1 = s(v1, u1)
  gammaJ_missing : C.gamma blockIndex ∈ MissingColors G phi v1
  blockIndex_ne : blockIndex ≠ D.gammaIndex d
  alpha0_ne_gamma : D.alpha0 ≠ C.gamma (D.gammaIndex d)
  alpha0_ne_gammaJ : D.alpha0 ≠ C.gamma blockIndex
  alpha0_ne_delta : D.alpha0 ≠ d.1
  gamma_ne_gammaJ : C.gamma (D.gammaIndex d) ≠ C.gamma blockIndex
  gamma_ne_delta : C.gamma (D.gammaIndex d) ≠ d.1
  gammaJ_ne_delta : C.gamma blockIndex ≠ d.1

end GoldbergSeymour

end
