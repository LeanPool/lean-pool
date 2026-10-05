/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.ChordlessCycles
public import LeanPool.StructuralGraphClasses.SplitExtension
public import LeanPool.StructuralGraphClasses.Threshold
public import LeanPool.StructuralGraphClasses.InducedPathFour

/-!
# The Földes–Hammer characterization of finite split graphs

Excluding induced `2K₂`, `C₄` and `C₅` makes every cycle of length at least
four have a chord. For finite graphs, the established simplicial reconstruction
then gives a split partition. Both directions use native induced containment.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Excluding the three split obstructions implies chordality, without finiteness. -/
theorem isChordal_of_forbidden_induced_subgraphs
    (hpair : ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G)
    (hfour : ¬(cycleGraph 4).IsIndContained G)
    (hfive : ¬(cycleGraph 5).IsIndContained G) : G.IsChordal := by
  intro v c hc hlen
  by_contra hn
  have hh : c.IsChordless := Walk.isChordless_iff_forall_mem_edges.mpr (by
    intro x y hx hy hxy
    by_contra hedge
    exact hn ⟨x, y, hx, hy, hxy, hedge⟩)
  by_cases hsix : 6 ≤ c.length
  · exact hpair (hc.twoK2_isIndContained_of_isChordless hh hsix)
  · have hsmall : c.length = 4 ∨ c.length = 5 := by omega
    have he := hc.cycleGraph_isIndContained_of_isChordless hh
    rcases hsmall with h | h
    · rw [h] at he
      exact hfour he
    · rw [h] at he
      exact hfive he

/-- **Földes–Hammer:** a finite graph is split iff it excludes induced `2K₂`, `C₄` and `C₅`. -/
theorem isSplit_iff_forbidden_induced_subgraphs [Finite V] :
    G.IsSplit ↔
      (¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) ∧
      (¬(cycleGraph 4).IsIndContained G) ∧ ¬(cycleGraph 5).IsIndContained G := by
  refine ⟨fun h => ⟨h.not_twoK2_isIndContained,
    h.not_cycleGraph_four_isIndContained, h.not_cycleGraph_five_isIndContained⟩, ?_⟩
  rintro ⟨hpair, hfour, hfive⟩
  exact IsChordal.isSplit_of_not_twoK2_isIndContained
    (isChordal_of_forbidden_induced_subgraphs hpair hfour hfive) hpair

/-- Four consecutive vertices in the five-cycle form an induced four-vertex path. -/
theorem pathGraph_four_isIndContained_cycleGraph_five :
    (pathGraph 4).IsIndContained (cycleGraph 5) := by
  refine ⟨⟨⟨fun i => (⟨i.val, by omega⟩ : Fin 5), ?_⟩, ?_⟩⟩
  · intro i j hij
    exact Fin.ext (congrArg (fun x : Fin 5 => x.val) hij)
  · intro i j
    rw [cycleGraph_adj', pathGraph_adj]
    fin_cases i <;> fin_cases j <;> decide

/-- A finite graph is threshold iff it excludes induced `2K₂`, `C₄` and `P₄`. -/
theorem isThreshold_iff_forbidden_induced_subgraphs [Finite V] :
    G.IsThreshold ↔
      (¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) ∧
      (¬(cycleGraph 4).IsIndContained G) ∧ ¬(pathGraph 4).IsIndContained G := by
  constructor
  · intro h
    obtain ⟨hs, hp⟩ := isThreshold_iff_isSplit_and_isP4Free.mp h
    exact ⟨hs.not_twoK2_isIndContained, hs.not_cycleGraph_four_isIndContained,
      hp.not_pathGraph_four_isIndContained⟩
  · rintro ⟨hpair, hfour, hpath⟩
    have hfive : ¬(cycleGraph 5).IsIndContained G :=
      fun h => hpath (pathGraph_four_isIndContained_cycleGraph_five.trans h)
    exact isThreshold_iff_isSplit_and_isP4Free.mpr
      ⟨isSplit_iff_forbidden_induced_subgraphs.mpr ⟨hpair, hfour, hfive⟩,
        isP4Free_iff_not_pathGraph_four_isIndContained.mpr hpath⟩

end SimpleGraph
