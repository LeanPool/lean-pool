/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Elementary
public import LeanPool.GoldbergSeymour.ScheideSmallHeightElementary

/-!
# Scheide Order Nine Parameters

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideOrderNineParameters {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hnonelementary : ¬ Elementary G) (horder : TashkinovOrder G < 11)
    (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N) :
    TashkinovOrder G = 9 ∧ ScheideGraphHeight G = 5 ∧ T.length = 8 ∧ N.height = 5 := by
  classical
  let : DecidableEq V := Classical.decEq V
  have hheight_ge : 5 ≤ ScheideGraphHeight G := by
    by_contra h
    have hsmall : ScheideGraphHeight G < 5 := by omega
    exact hnonelementary
      (ScheideSmallHeightElementary G k hcritical hindex hdegree
        hnoisolated hsmall)
  have hheight_le : ScheideGraphHeight G ≤ TashkinovOrder G - 4 := by
    by_contra h
    have hlarge : TashkinovOrder G - 4 < ScheideGraphHeight G := by omega
    exact hnonelementary
      (ScheideLargeHeightElementary G k hcritical hindex hdegree
        hnoisolated hlarge)
  have horder_data := ScheideGlobalMaximumOrder G k e0 phi T N.global
  have hheight_odd : Odd (ScheideGraphHeight G) :=
    (ScheideGraphHeightOdd G k e0 phi T N.global).2
  have horder_odd : Odd (TashkinovOrder G) := by
    rw [horder_data.1]
    exact horder_data.2.2.1
  have hcard : (TreeSequenceVertexSet T).card = T.length + 1 := by
    unfold TreeSequenceVertexSet
    rw [Finset.card_image_of_injective Finset.univ T.vertex_injective]
    simp
  rcases hheight_odd with ⟨a, ha⟩
  rcases horder_odd with ⟨b, hb⟩
  have horder_eq : TashkinovOrder G = 9 := by omega
  have hheight_eq : ScheideGraphHeight G = 5 := by omega
  have hlength_eq : T.length = 8 := by omega
  have hNheight : N.height = 5 := by
    rw [hbalanced.1, hheight_eq]
  exact ⟨horder_eq, hheight_eq, hlength_eq, hNheight⟩

end GoldbergSeymour

end
