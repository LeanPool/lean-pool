/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MissingColors

/-!
# Td Earlier PEWitness Identification

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TdEarlierPEWitnessIdentification {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (T : TreeSequence G e0) (C Cstar : Finset (Fin k))
    (phi phiStar : PartialEdgeColoring E k)
    (choice : MaximumDefectiveChoice G e0 T C phi)
    (choiceStar : MaximumDefectiveChoice G e0 T Cstar phiStar)
    (gamma gammaStar : Fin k)
    (post postStar : PartialEdgeColoring E k)
    (hedges : ({choice.edge} : Finset E) = {choiceStar.edge})
    (hpairs : ({choice.color, gamma} : Finset (Fin k)) =
      {choiceStar.color, gammaStar})
    (hmissing : MissingColors G post choice.vertex =
      MissingColors G postStar choiceStar.vertex)
    (hdelta : choice.color ∈ MissingColors G post choice.vertex)
    (hgamma : gamma ∉ MissingColors G post choice.vertex)
    (hdeltaStar : choiceStar.color ∈
      MissingColors G postStar choiceStar.vertex)
    (hgammaStar : gammaStar ∉
      MissingColors G postStar choiceStar.vertex) :
    choiceStar.edge = choice.edge ∧
      choiceStar.vertex = choice.vertex ∧
        choiceStar.otherEndpoint = choice.otherEndpoint ∧
          choiceStar.color = choice.color ∧ gammaStar = gamma := by
  classical
  have hedge : choiceStar.edge = choice.edge := by
    apply Finset.mem_singleton.mp
    rw [hedges]
    exact Finset.mem_singleton_self _
  have hends : s(choice.vertex, choice.otherEndpoint) =
      s(choiceStar.vertex, choiceStar.otherEndpoint) := by
    calc
      s(choice.vertex, choice.otherEndpoint) = G.ends choice.edge :=
        choice.edgeEnds.symm
      _ = G.ends choiceStar.edge := congrArg G.ends hedge.symm
      _ = s(choiceStar.vertex, choiceStar.otherEndpoint) := choiceStar.edgeEnds
  have hvertex : choiceStar.vertex = choice.vertex := by
    rcases (Sym2.eq_iff.mp hends) with hstraight | hcross
    · exact hstraight.1.symm
    · exfalso
      have hin : choice.vertex ∈ TreeSequenceVertexSet T :=
        choice.vertexDefective.1
      have hout : choiceStar.otherEndpoint ∉ TreeSequenceVertexSet T := by
        exact choiceStar.otherOutside
      apply hout
      exact hcross.1 ▸ hin
  have hother : choiceStar.otherEndpoint = choice.otherEndpoint := by
    rcases (Sym2.eq_iff.mp hends) with hstraight | hcross
    · exact hstraight.2.symm
    · exfalso
      have hin : choiceStar.vertex ∈ TreeSequenceVertexSet T := by
        exact choiceStar.vertexDefective.1
      have hout : choice.otherEndpoint ∉ TreeSequenceVertexSet T :=
        choice.otherOutside
      apply hout
      exact hcross.2 ▸ hin
  have hmissing' : MissingColors G post choice.vertex =
      MissingColors G postStar choiceStar.vertex := by
    exact hmissing
  have hcolor : choiceStar.color = choice.color := by
    have hnot : choiceStar.color ≠ gamma := by
      intro heq
      apply hgamma
      have hd : choiceStar.color ∈ MissingColors G post choice.vertex :=
        hmissing'.symm ▸ hdeltaStar
      exact heq ▸ hd
    have hcases : choice.color = choiceStar.color ∨
        choice.color = gammaStar := by
      have hm : choice.color ∈ ({choiceStar.color, gammaStar} : Finset (Fin k)) := by
        exact hpairs ▸ Finset.mem_insert.mpr (Or.inl rfl)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hcases with hcase | hcase
    · exact hcase.symm
    · exfalso
      apply hgammaStar
      have hd : choice.color ∈ MissingColors G postStar choiceStar.vertex :=
        hmissing' ▸ hdelta
      exact hcase.symm ▸ hd
  have hgamma' : gammaStar = gamma := by
    have hpair : ({choice.color, gamma} : Finset (Fin k)) =
        {choiceStar.color, gammaStar} := hpairs
    rw [hcolor] at hpair
    have hmem : gammaStar ∈ ({choice.color, gamma} : Finset (Fin k)) := by
      have hm : gammaStar ∈ ({choice.color, gammaStar} : Finset (Fin k)) :=
        Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      exact hpair.symm ▸ hm
    have hcases : gammaStar = choice.color ∨ gammaStar = gamma := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    rcases hcases with h | h
    · exfalso
      apply hgammaStar
      have hd : choice.color ∈ MissingColors G postStar choiceStar.vertex :=
        hmissing' ▸ hdelta
      exact h.symm ▸ hd
    · exact h
  exact ⟨hedge, hvertex, hother, hcolor, hgamma'⟩

end GoldbergSeymour

end
