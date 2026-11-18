/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DefectiveColors

public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder

/-!
# Scheide Global Maximum Unused

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideGlobalMaximumUnused {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    Disjoint (DefectiveColors G phi (TreeSequenceVertexSet T))
        (TreeUsedColors phi T) ∧
      Disjoint (TreeFreeColors phi T) (TreeUsedColors phi T) := by
  classical
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  constructor
  · rw [Finset.disjoint_left]
    intro alpha hdef hused
    have hcard : 2 ≤ (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card := by
      change alpha ∈ Finset.univ.filter
        (fun alpha => DefectiveColor G phi (TreeSequenceVertexSet T) alpha) at hdef
      exact (Finset.mem_filter.mp hdef).2
    have hpos : 0 < (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card :=
      lt_of_lt_of_le Nat.zero_lt_two hcard
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
    have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
      exact (Finset.mem_filter.mp hf).1
    have hfc : phi f = some alpha := by
      exact (Finset.mem_filter.mp hf).2
    have hnot : ∀ v, v ∈ TreeSequenceVertexSet T →
        alpha ∉ MissingColors G phi v := by
      intro v hv hm
      exact (hclosed hfb hv hfc) hm
    have htree := hglobal.2.1
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hused
    obtain ⟨j, hj, hje⟩ := hused
    obtain ⟨i, c, hcolor, hmiss⟩ := htree j hj
    have hac : c = alpha := by
      have hac' : alpha = c := by simpa [hje] using hcolor
      exact hac'.symm
    have hv : T.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) ∈
        TreeSequenceVertexSet T := by
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    exact hnot _ hv (hac ▸ hmiss)
  · change Disjoint (TreeMissingColors phi T \ TreeUsedColors phi T)
      (TreeUsedColors phi T)
    exact Finset.sdiff_disjoint

end GoldbergSeymour

end
