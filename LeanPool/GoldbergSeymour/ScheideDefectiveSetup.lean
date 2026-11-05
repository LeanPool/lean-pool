/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.TreeMissingColors

/-!
# Scheide Defective Setup

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/--
Initial and replacement defective-color paths with their last tree vertices and boundary edges. -/
structure ScheideDefectiveSetup {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) where
  /-- A color missing at the initial base vertex and distinct from every block color. -/
  alpha0 : Fin k
  alpha0_missing_at_y0 :
    alpha0 ∈ MissingColors G phi (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)
  alpha0_not_block : ∀ i : Fin C.s, alpha0 ≠ C.gamma i
  /-- The last inside vertex on the initial path for each defective color. -/
  v0 : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) } → V
  /-- The boundary edge following that last inside vertex. -/
  f0 : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) } → E
  /-- The outside endpoint immediately following the chosen boundary edge. -/
  u0 : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) } → V
  /-- The block index supplying the missing color for each defective-color path. -/
  gammaIndex : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) } → Fin C.s
  /-- The outside endpoint of the initial defective-color path. -/
  initialZ : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) } → V
  /-- The initial spanning path for each defective-color component. -/
  initialPath :
    ∀ d,
      (TwoColorIncidenceGraph G phi alpha0 d.1).Walk
        (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) (Sum.inl (initialZ d))
  initial_path_full :
    ∀ d,
      ScheideDefectiveChainPath T phi alpha0 d.1
        (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩) (initialZ d) (initialPath d)
  /-- The position of the last inside vertex on each initial path. -/
  v0Index : ∀ d, Fin ((initialPath d).length + 1)
  /-- The position of the following boundary edge on each initial path. -/
  f0Index : ∀ d, Fin ((initialPath d).length + 1)
  /-- The position of the following outside endpoint on each initial path. -/
  u0Index : ∀ d, Fin ((initialPath d).length + 1)
  v0_at_index : ∀ d, (initialPath d).getVert (v0Index d).val = Sum.inl (v0 d)
  f0_at_index : ∀ d, (initialPath d).getVert (f0Index d).val = Sum.inr (f0 d)
  u0_at_index : ∀ d, (initialPath d).getVert (u0Index d).val = Sum.inl (u0 d)
  successive_indices :
    ∀ d, (f0Index d).val = (v0Index d).val + 1 ∧ (u0Index d).val = (v0Index d).val + 2
  v0_is_last_tree_vertex :
    ∀ d,
      ∀ r : Fin ((initialPath d).length + 1),
        (v0Index d).val < r.val →
          ∀ w : V, (initialPath d).getVert r.val = Sum.inl w → w ∉ TreeSequenceVertexSet T
  v0_is_exit : ∀ d, v0 d ∈ ScheideExitVertices T phi
  gamma_missing_at_v0 : ∀ d, C.gamma (gammaIndex d) ∈ MissingColors G phi (v0 d)
  f0_color : ∀ d, phi (f0 d) = some d.1
  f0_ends : ∀ d, G.ends (f0 d) = s(v0 d, u0 d)
  u0_outside : ∀ d, u0 d ∉ TreeSequenceVertexSet T
  v0_on_initial_component :
    ∀ d, Sum.inl (v0 d) ∈ TwoColorComponent G phi alpha0 d.1 (Sum.inl (C.y ⟨0, lt_of_lt_of_le
        Nat.zero_lt_two C.p_ge_two⟩))
  f0_on_initial_component :
    ∀ d, Sum.inr (f0 d) ∈ TwoColorComponent G phi alpha0 d.1 (Sum.inl (C.y ⟨0, lt_of_lt_of_le
        Nat.zero_lt_two C.p_ge_two⟩))
  /-- The outside endpoint of the replacement defective-color path. -/
  replacementZ : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) } → V
  /-- The replacement spanning path for each defective-color component. -/
  replacementPath :
    ∀ d,
      (TwoColorIncidenceGraph G phi (C.gamma (gammaIndex d)) d.1).Walk (Sum.inl (v0 d))
        (Sum.inl (replacementZ d))
  replacement_path_full :
    ∀ d,
      ScheideDefectiveChainPath T phi (C.gamma (gammaIndex d)) d.1 (v0 d) (replacementZ d)
        (replacementPath d)

end GoldbergSeymour

end
