/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Critical
public import LeanPool.GoldbergSeymour.Elementary
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.GlobalMaximumTripleExists
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ScheideBalancedExists
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGraphHeight
public import LeanPool.GoldbergSeymour.ScheideGraphHeightOdd
public import LeanPool.GoldbergSeymour.ScheideLargeHeightFullTrunk
public import LeanPool.GoldbergSeymour.ScheideLargeHeightOneTailPair
public import LeanPool.GoldbergSeymour.TashkinovOrder
public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Scheide Large Height Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideLargeHeightElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hlarge : TashkinovOrder G - 4 < ScheideGraphHeight G) :
    Elementary G := by
  classical
  let : DecidableEq V := Classical.decEq V
  obtain ⟨e0, phi, T, hglobal⟩ :=
    GlobalMaximumTripleExists G k hcritical hindex hdegree
  obtain ⟨e1, psi, S, N, hbalanced⟩ :=
    ScheideBalancedExists G k e0 phi T hglobal
  have hcard : (TreeSequenceVertexSet S).card = S.length + 1 := by
    unfold TreeSequenceVertexSet
    rw [Finset.card_image_of_injective Finset.univ S.vertex_injective]
    simp
  have hheight_le : ScheideGraphHeight G ≤ TashkinovOrder G := by
    calc
      ScheideGraphHeight G = N.height := hbalanced.1.symm
      _ ≤ S.length + 1 := N.height_upper
      _ = (TreeSequenceVertexSet S).card := hcard.symm
      _ = TashkinovOrder G := N.global.2.2
  have hheight_odd : Odd (ScheideGraphHeight G) :=
    (ScheideGraphHeightOdd G k e0 phi T hglobal).2
  have horder_odd : Odd (TashkinovOrder G) :=
    N.global.2.2 ▸
      (ScheideGlobalMaximumOrder G k e1 psi S N.global).2.2.1
  rcases hheight_odd with ⟨a, ha⟩
  rcases horder_odd with ⟨b, hb⟩
  have hcases : ScheideGraphHeight G = TashkinovOrder G ∨
      ScheideGraphHeight G + 2 = TashkinovOrder G := by
    omega
  rcases hcases with heq | heq
  · exact ScheideLargeHeightFullTrunk G k e1 psi S N hbalanced
      hnoisolated heq
  · exact ScheideLargeHeightOneTailPair G k e1 psi S N hbalanced
      hnoisolated heq

end GoldbergSeymour

end
