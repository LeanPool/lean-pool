/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideBalancedCandidate

/-!
# Scheide Balanced Candidate Normal Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideBalancedCandidateNormalTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hS : ScheideBalancedCandidate N S)
    (hvertices : TreeSequenceVertexSet S = TreeSequenceVertexSet T) :
    ∃ N' : NormalGlobalMaximumTriple G k e0 phi S,
      N'.height = N.height := by
  classical
  have Tpos : 1 ≤ T.length := T.positive
  have Spos : 1 ≤ S.length := S.positive
  have vertexCard : ∀ R : TreeSequence G e0,
      (TreeSequenceVertexSet R).card = R.length + 1 := by
    intro R
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      R.vertex_injective]
  have lengthEq : S.length = T.length := by
    have h := congrArg Finset.card hvertices
    rw [vertexCard S, vertexCard T] at h
    omega
  have trunkData := hS.exactTrunk
  rcases trunkData with ⟨trunkBound, trunkVertices, trunkEdges⟩
  have trunkLength : (NormalTripleTrunk N).length = N.height - 1 := by
    rfl
  have vertexEq : ∀ i : Fin N.height,
      S.vertex ⟨i.val, by omega⟩ =
        T.vertex (Fin.castLE N.height_upper i) := by
    intro i
    have hv := trunkVertices ⟨i.val, by omega⟩
    have htr := show (NormalTripleTrunk N).vertex
        ⟨i.val, by omega⟩ = T.vertex (Fin.castLE N.height_upper i) by
      unfold NormalTripleTrunk TreeSequencePrefix
      rfl
    simpa only [Fin.castLE] using hv.trans htr
  have edgeEq : ∀ j : Fin S.length, 1 ≤ j.val → j.val + 2 ≤ N.height →
      S.edge j = T.edge ⟨j.val, by omega⟩ := by
    intro j hjlow hjhigh
    let jj : Fin (NormalTripleTrunk N).length := ⟨j.val, by
      rw [trunkLength]
      omega⟩
    have he := trunkEdges jj
    unfold NormalTripleTrunk TreeSequencePrefix at he
    have hsidx : Fin.castLE trunkBound jj = j := by
      apply Fin.ext
      dsimp [Fin.castLE]
    have htidx : (⟨j.val, by omega⟩ : Fin T.length) =
        Fin.castLE (by rw [trunkLength]; omega) jj := by
      apply Fin.ext
      dsimp [Fin.castLE]
    calc
      S.edge j = S.edge (Fin.castLE trunkBound jj) := congrArg S.edge hsidx.symm
      _ = (NormalTripleTrunk N).edge jj := he
      _ = T.edge (Fin.castLE (by rw [trunkLength]; omega) jj) := by
        unfold NormalTripleTrunk TreeSequencePrefix
        rfl
      _ = T.edge ⟨j.val, by omega⟩ := congrArg T.edge htidx.symm
  have zeroEq : S.vertex ⟨0, Nat.zero_lt_succ S.length⟩ =
      T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
    have hp := N.height_lower
    simpa only [Fin.castLE] using vertexEq ⟨0, by omega⟩
  have oneEq : S.vertex ⟨1, Nat.lt_succ_iff.mpr Spos⟩ =
      T.vertex ⟨1, Nat.lt_succ_iff.mpr Tpos⟩ := by
    have hp := N.height_lower
    simpa only [Fin.castLE] using vertexEq ⟨1, by omega⟩
  have lastEq : ∀ i : Fin N.height,
      S.vertex ⟨i.val, by omega⟩ = T.vertex (Fin.castLE N.height_upper ⟨i.val, by omega⟩) := by
    intro i
    exact vertexEq ⟨i.val, by omega⟩
  have cardEq : (TreeSequenceVertexSet S).card = TashkinovOrder G := by
    rw [hvertices]
    exact N.global.2.2
  have pathTransport :
    ∀ {u v u' v' : Sum V E} (p : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk u v), p.IsPath
        → u = u' → v = v' →
    ∃ q : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk u' v', q.IsPath ∧ q.length = p.length
        ∧ q.support = p.support := by
    intro u v u' v' p hp hu hv
    cases hu
    cases hv
    exact ⟨p, hp, rfl, rfl⟩
  obtain ⟨transportedPath, transportedIsPath, transportedLength,
    transportedSupport⟩ := pathTransport N.closingPath N.closingPath_isPath
      (congrArg Sum.inl oneEq.symm) (congrArg Sum.inl zeroEq.symm)
  have pathIs :
      ((transportedPath :
        (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk
          (Sum.inl (S.vertex ⟨1, Nat.lt_succ_iff.mpr Spos⟩))
          (Sum.inl (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩))).IsPath) := by
    simpa only using transportedIsPath
  have pathLength :
      (transportedPath :
        (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk
          (Sum.inl (S.vertex ⟨1, Nat.lt_succ_iff.mpr Spos⟩))
          (Sum.inl (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩))).length =
        N.closingPath.length := by
    simpa only using transportedLength
  have pathSupport :
      (transportedPath :
        (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk
          (Sum.inl (S.vertex ⟨1, Nat.lt_succ_iff.mpr Spos⟩))
          (Sum.inl (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩))).support =
        N.closingPath.support := by
    simpa only using transportedSupport
  let hnew : NormalGlobalMaximumTriple G k e0 phi S := by
    refine
      { global := ⟨N.global.1, hS.tashkinov, cardEq⟩
        height := N.height
        height_lower := N.height_lower
        height_upper := by
          rw [lengthEq]
          exact N.height_upper
        alpha := N.alpha
        beta := N.beta
        alpha_missing := ?_
        beta_missing := ?_
        closingEdge := N.closingEdge
        lastIndex := ⟨N.lastIndex.val, by
          rw [lengthEq]
          exact N.lastIndex.isLt⟩
        lastIndex_height := N.lastIndex_height
        closing_ends := ?_
        closingPath := by simpa only using transportedPath
        closingPath_isPath := ?_
        closingPath_length := ?_
        closingPath_vertices := ?_
        closingPath_edges := ?_
        trunk_edge_ends := ?_ }
    · rw [zeroEq]
      exact N.alpha_missing
    · rw [oneEq]
      exact N.beta_missing
    · have hlastIndex : N.lastIndex.val < N.height :=
        Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) N.lastIndex_height
      have hlast := lastEq ⟨N.lastIndex.val, hlastIndex⟩
      rw [hlast, zeroEq]
      exact N.closing_ends
    · simpa only using pathIs
    · rw [pathLength]
      exact N.closingPath_length
    · intro v
      constructor
      · intro hv
        have hv' := (N.closingPath_vertices v).mp (by
          rw [← pathSupport]
          exact hv)
        rcases hv' with ⟨i, hi⟩
        refine (show ∃ i : Fin N.height, v = S.vertex ⟨i.val, by omega⟩ from ?_)
        refine ⟨i, hi.trans (vertexEq i).symm⟩
      · intro hv
        have hv' : ∃ i : Fin N.height,
            v = T.vertex (Fin.castLE N.height_upper i) := by
          rcases hv with ⟨i, hi⟩
          exact ⟨i, hi.trans (vertexEq i)⟩
        rw [pathSupport]
        exact (N.closingPath_vertices v).mpr hv'
    · intro f
      constructor
      · intro hf
        have hf' := (N.closingPath_edges f).mp (by
          rw [← pathSupport]
          exact hf)
        rcases hf' with hclose | ⟨j, hj, hsj, hf⟩
        · exact Or.inl hclose
        · right
          refine ⟨⟨j.val, by omega⟩, hj, hsj, ?_⟩
          calc
            f = T.edge j := hf
            _ = S.edge ⟨j.val, by omega⟩ := (edgeEq ⟨j.val, by omega⟩ hj hsj).symm
      · intro hf
        rw [pathSupport]
        apply (N.closingPath_edges f).mpr
        rcases hf with hclose | ⟨j, hj, hsj, hf⟩
        · exact Or.inl hclose
        · right
          refine ⟨⟨j.val, by omega⟩, hj, hsj, ?_⟩
          calc
            f = S.edge j := hf
            _ = T.edge ⟨j.val, by omega⟩ := edgeEq j hj hsj
    · intro j hj hsj
      have he := N.trunk_edge_ends ⟨j.val, by omega⟩ hj hsj
      calc
        G.ends (S.edge j) = G.ends (T.edge ⟨j.val, by omega⟩) :=
          congrArg G.ends (edgeEq j hj hsj)
        _ = s(S.vertex ⟨j.val, by omega⟩, S.vertex j.succ) := by
          have hcur : S.vertex ⟨j.val, by omega⟩ =
              T.vertex (Fin.castLE N.height_upper ⟨j.val, by omega⟩) :=
            vertexEq ⟨j.val, by omega⟩
          have hnext : S.vertex j.succ =
              T.vertex ⟨j.val + 1, by omega⟩ := by
            have hs : j.succ = (⟨j.val + 1, by omega⟩ : Fin (S.length + 1)) := by
              apply Fin.ext
              rfl
            have ht : (⟨j.val + 1, by omega⟩ : Fin (T.length + 1)) =
                Fin.castLE N.height_upper ⟨j.val + 1, by omega⟩ := by
              apply Fin.ext
              dsimp [Fin.castLE]
            calc
              S.vertex j.succ = S.vertex ⟨j.val + 1, by omega⟩ := congrArg S.vertex hs
              _ = T.vertex (Fin.castLE N.height_upper ⟨j.val + 1, by omega⟩) :=
                vertexEq ⟨j.val + 1, by omega⟩
              _ = T.vertex ⟨j.val + 1, by omega⟩ := congrArg T.vertex ht.symm
          rw [hcur, hnext]
          convert he using 1; rfl
  exact ⟨hnew, rfl⟩

end GoldbergSeymour

end
