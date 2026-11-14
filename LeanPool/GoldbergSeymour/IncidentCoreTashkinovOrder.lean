/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentCoreKTriple
public import LeanPool.GoldbergSeymour.IncidentCoreTreeTransport
public import LeanPool.GoldbergSeymour.TashkinovOrder

/-!
# Incident Core Tashkinov Order

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreTashkinovOrder {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) :
    TashkinovOrder (IncidentCore G) = TashkinovOrder G := by
  classical
  have hindex := (IncidentCoreChromaticIndex G).1
  have hforward := (IncidentCoreTreeTransport G).1
  have hbackward := (IncidentCoreTreeTransport G).2
  let k := ChromaticIndex G - 1
  unfold TashkinovOrder
  dsimp only
  apply Nat.le_antisymm
  · apply Finset.max'_le
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Nat.zero_le _
    · rcases Finset.mem_filter.mp hn with ⟨hnrange, ⟨e0, phi, Tc, htriple, htree, hcard⟩⟩
      obtain ⟨T, hlen, hvertices, hedges, hsize, htreeeq⟩ :=
        hbackward e0 (ChromaticIndex (IncidentCore G) - 1) phi Tc
      have hbound : (TreeSequenceVertexSet T).card ≤ Fintype.card V := by
        simpa [TreeSequenceVertexSet, Finset.card_image_of_injective _ T.vertex_injective] using
          (Fintype.card_le_of_injective T.vertex T.vertex_injective)
      apply Finset.le_max' _ _
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · have hmem : ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex (IncidentCore G) - 1))
            (S : TreeSequence G e),
            KTriple G (ChromaticIndex (IncidentCore G) - 1) e p ∧
              TashkinovTree G e p S ∧ (TreeSequenceVertexSet S).card = n := by
          refine ⟨e0, phi, T, ?_, htreeeq.mpr htree, hsize.symm.trans hcard⟩
          exact (IncidentCoreKTriple G (ChromaticIndex (IncidentCore G) - 1) e0 phi).mp htriple
        have bridge :
            (∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex (IncidentCore G) - 1))
              (S : TreeSequence G e),
              KTriple G (ChromaticIndex (IncidentCore G) - 1) e p ∧
                TashkinovTree G e p S ∧ (TreeSequenceVertexSet S).card = n) =
            (∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
              (S : TreeSequence G e),
              KTriple G (ChromaticIndex G - 1) e p ∧
                TashkinovTree G e p S ∧ (TreeSequenceVertexSet S).card = n) := by
          exact congrArg (fun q => ∃ (e : E) (p : PartialEdgeColoring E (q - 1))
            (S : TreeSequence G e), KTriple G (q - 1) e p ∧
              TashkinovTree G e p S ∧ (TreeSequenceVertexSet S).card = n) hindex
        exact bridge ▸ hmem
  · apply Finset.max'_le
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Nat.zero_le _
    · rcases Finset.mem_filter.mp hn with ⟨hnrange, ⟨e0, phi, T, htriple, htree, hcard⟩⟩
      obtain ⟨Tc, hlen, hvertices, hedges, hsize, htreeeq⟩ :=
        hforward e0 k phi T
      have hbound : (TreeSequenceVertexSet Tc).card ≤ Fintype.card (IncidentVertex G) := by
        simpa [TreeSequenceVertexSet, Finset.card_image_of_injective _ Tc.vertex_injective] using
          (Fintype.card_le_of_injective Tc.vertex Tc.vertex_injective)
      apply Finset.le_max' _ _
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · have hmem : ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
            (S : TreeSequence (IncidentCore G) e),
            KTriple (IncidentCore G) (ChromaticIndex G - 1) e p ∧
              TashkinovTree (IncidentCore G) e p S ∧ (TreeSequenceVertexSet S).card = n := by
          refine ⟨e0, phi, Tc, (IncidentCoreKTriple G k e0 phi).mpr htriple,
            htreeeq.mpr htree, hsize.trans hcard⟩
        have bridge :
            (∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
              (S : TreeSequence (IncidentCore G) e),
              KTriple (IncidentCore G) (ChromaticIndex G - 1) e p ∧
                TashkinovTree (IncidentCore G) e p S ∧ (TreeSequenceVertexSet S).card = n) =
            (∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex (IncidentCore G) - 1))
              (S : TreeSequence (IncidentCore G) e),
              KTriple (IncidentCore G) (ChromaticIndex (IncidentCore G) - 1) e p ∧
                TashkinovTree (IncidentCore G) e p S ∧ (TreeSequenceVertexSet S).card = n) := by
          exact congrArg (fun q => ∃ (e : E) (p : PartialEdgeColoring E (q - 1))
            (S : TreeSequence (IncidentCore G) e), KTriple (IncidentCore G) (q - 1) e p ∧
              TashkinovTree (IncidentCore G) e p S ∧ (TreeSequenceVertexSet S).card = n) hindex.symm
        exact bridge ▸ hmem

end GoldbergSeymour

end
