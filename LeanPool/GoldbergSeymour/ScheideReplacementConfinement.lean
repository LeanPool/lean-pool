/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideLastExitPath
public import LeanPool.GoldbergSeymour.ScheideReplacementBoundaryUnique
public import LeanPool.GoldbergSeymour.ScheideReplacementExitNotDefective
public import LeanPool.GoldbergSeymour.ScheideReplacementPathPrefix
public import LeanPool.GoldbergSeymour.ScheideSymmetricDefectiveInternal
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Scheide Replacement Confinement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem ScheideReplacementConfinement_hgraph_272.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (alpha : Fin k) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))), alpha ≠ (↑d
        : Fin k) → alpha ≠ C.gamma (D.gammaIndex d) → D.alpha0 ≠ C.gamma (D.gammaIndex d) →
        D.alpha0 ≠ (↑d : Fin k) → (
    ∀ (c : Fin k), c ≠ C.gamma (D.gammaIndex d) → c ≠ (↑d : Fin k) →
    ∀ (f : E), TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)) f = some c ↔ phi f = some c) → TwoColorIncidenceGraph G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) D.alpha0 alpha =
        TwoColorIncidenceGraph G phi D.alpha0 alpha := by
  classical
  intro V E _ _ _ G k e0 phi T C D alpha d hAlphaDelta hAlphaGamma hAlpha0Gamma hAlpha0Delta
      colorFixed
  ext x y
  cases x with
  | inl vx =>
      cases y with
      | inl vy => rfl
      | inr e =>
          simp only [TwoColorIncidenceGraph]
          constructor <;> rintro ⟨hi, hc⟩ <;> refine ⟨hi, ?_⟩
          · rcases hc with hc | hc
            · exact Or.inl
                ((colorFixed D.alpha0 hAlpha0Gamma hAlpha0Delta e).mp hc)
            · exact Or.inr ((colorFixed alpha hAlphaGamma hAlphaDelta e).mp hc)
          · rcases hc with hc | hc
            · exact Or.inl
                ((colorFixed D.alpha0 hAlpha0Gamma hAlpha0Delta e).mpr hc)
            · exact Or.inr ((colorFixed alpha hAlphaGamma hAlphaDelta e).mpr hc)
  | inr e =>
      cases y with
      | inl vy =>
          simp only [TwoColorIncidenceGraph]
          constructor <;> rintro ⟨hi, hc⟩ <;> refine ⟨hi, ?_⟩
          · rcases hc with hc | hc
            · exact Or.inl
                ((colorFixed D.alpha0 hAlpha0Gamma hAlpha0Delta e).mp hc)
            · exact Or.inr ((colorFixed alpha hAlphaGamma hAlphaDelta e).mp hc)
          · rcases hc with hc | hc
            · exact Or.inl
                ((colorFixed D.alpha0 hAlpha0Gamma hAlpha0Delta e).mpr hc)
            · exact Or.inr ((colorFixed alpha hAlphaGamma hAlphaDelta e).mpr hc)
      | inr f => rfl

theorem ScheideReplacementConfinement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (L : ScheideLastExitPath G k e0 phi T C D R alpha)
    (hlast : L.lastInside ∉ TreeSequenceVertexSet T) :
    ∃ d : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) },
    L.lastInside ∈ ({(R d).u1, (R d).u2} : Finset V) ∧
      TwoColorIncidenceGraph G
            (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d)))
            D.alpha0 alpha =
          TwoColorIncidenceGraph G phi D.alpha0 alpha ∧
        (∀
            c ∈
              TreeUsedColors
                (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
                  (Sum.inl (D.v0 d)))
                (R d).replacementTree,
            ∃
              z ∈
                TreeSequenceVertexSet T \
                  {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1},
              c ∈
                MissingColors G
                  (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
                    (Sum.inl (D.v0 d)))
                  z) ∧
          (∃ beta,
              beta ∈
                  MissingColors G
                    (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
                      (Sum.inl (D.v0 d)))
                    L.lastInside ∧
                beta ∈
                  TreeFreeColors
                    (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
                      (Sum.inl (D.v0 d)))
                    (R d).replacementTree) ∧
            alpha ∉
                DefectiveColors G
                  (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
                    (Sum.inl (D.v0 d)))
                  (TreeSequenceVertexSet (R d).replacementTree) ∧
              (∀ (j : Fin (L.path.length + 1)),
                  j.val ≤ L.lastIndex.val →
                    ∀ x : V,
                      L.path.getVert j.val = Sum.inl x →
                        x ∈ TreeSequenceVertexSet (R d).replacementTree) ∧
                ∀ f : E,
                  f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧
                      Sum.inr f ∈
                        TwoColorComponent G phi D.alpha0 alpha
                          (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) →
                    f = L.crossing := by
  classical
  have hpairUnion : L.lastInside ∈ Finset.univ.biUnion
      (fun d => ({(R d).u1, (R d).u2} : Finset V)) := by
    have hmem := L.lastInsideMem
    rw [ScheideEnlargedVertexSet, Finset.mem_union] at hmem
    exact hmem.resolve_left hlast
  obtain ⟨d, -, hpair⟩ := Finset.mem_biUnion.mp hpairUnion
  let X := ScheideEnlargedVertexSet R
  have hTreeSub : TreeSequenceVertexSet T ⊆ X := by
    intro v hv
    simp [X, ScheideEnlargedVertexSet, hv]
  have hu1X : (R d).u1 ∈ X := by
    change (R d).u1 ∈ ScheideEnlargedVertexSet R
    rw [ScheideEnlargedVertexSet, Finset.mem_union]
    right
    exact Finset.mem_biUnion.mpr
      ⟨d, Finset.mem_univ d, by simp⟩
  have hu2X : (R d).u2 ∈ X := by
    change (R d).u2 ∈ ScheideEnlargedVertexSet R
    rw [ScheideEnlargedVertexSet, Finset.mem_union]
    right
    exact Finset.mem_biUnion.mpr
      ⟨d, Finset.mem_univ d, by simp⟩
  have internalNotBoundary (f : E) (a b : V)
      (hends : G.ends f = s(a, b)) (ha : a ∈ X) (hb : b ∈ X) :
      f ∉ BoundaryEdges G X := by
    intro hboundary
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      at hboundary
    obtain ⟨x, hx, y, hy, hxy⟩ := hboundary
    have hpairs : s(a, b) = s(x, y) := hends.symm.trans hxy
    rcases Sym2.eq_iff.mp hpairs with h | h
    · exact hy (by simpa [← h.2] using hb)
    · exact hy (by simpa [← h.1] using ha)
  have hcrossIncident : Incident G L.lastInside L.crossing := by
    have hadj := L.path.adj_getVert_succ
      (i := L.lastIndex.val) (by
        have h := L.followingVertex
        omega)
    rw [L.lastInsideAt, L.crossingAt] at hadj
    simpa only [TwoColorIncidenceGraph] using hadj.1
  obtain ⟨fDelta, hfDeltaColor, hfDeltaIncident, hfDeltaNe⟩ :
      ∃ f : E, phi f = some d.1 ∧ Incident G L.lastInside f ∧
        f ≠ L.crossing := by
    have hp := hpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hv | hv
    · refine ⟨(R d).f1, (R d).f1_color, ?_, ?_⟩
      · rw [hv]
        change (R d).u1 ∈ G.ends (R d).f1
        rw [(R d).f1_ends]
        simp
      · intro heq
        have hinter : (R d).f1 ∉ BoundaryEdges G X :=
          internalNotBoundary (R d).f1 (R d).v1 (R d).u1
            (R d).f1_ends
            (hTreeSub (Finset.mem_sdiff.mp (R d).v1_in_remainder).1) hu1X
        exact hinter (heq ▸ (by simpa only [X] using L.crossingBoundary))
    · refine ⟨(R d).f2, (R d).f2_color, ?_, ?_⟩
      · rw [hv]
        change (R d).u2 ∈ G.ends (R d).f2
        rw [(R d).f2_ends]
        simp
      · intro heq
        have hinter : (R d).f2 ∉ BoundaryEdges G X :=
          internalNotBoundary (R d).f2 (R d).v2 (R d).u2
            (R d).f2_ends
            (hTreeSub (Finset.mem_sdiff.mp (R d).v2_in_remainder).1) hu2X
        exact hinter (heq ▸ (by simpa only [X] using L.crossingBoundary))
  obtain ⟨fGamma, hfGammaColor, hfGammaEnds⟩ :=
    (ScheideSymmetricDefectiveInternal G k e0 phi T C D d (R d)).2
  have hfGammaIncident : Incident G L.lastInside fGamma := by
    have hp := hpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hv | hv
    · rw [hv]
      change (R d).u1 ∈ G.ends fGamma
      rw [hfGammaEnds]
      simp
    · rw [hv]
      change (R d).u2 ∈ G.ends fGamma
      rw [hfGammaEnds]
      simp
  have hfGammaNe : fGamma ≠ L.crossing := by
    intro heq
    have hinter : fGamma ∉ BoundaryEdges G X :=
      internalNotBoundary fGamma (R d).u1 (R d).u2 hfGammaEnds hu1X hu2X
    exact hinter (heq ▸ (by simpa only [X] using L.crossingBoundary))
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have hAlphaDelta : alpha ≠ d.1 := by
    intro h
    have hnot := hproper hfDeltaNe.symm
      ⟨L.lastInside, hcrossIncident, hfDeltaIncident⟩ L.crossingColor
    exact hnot (by simpa [h] using hfDeltaColor)
  have hAlphaGamma : alpha ≠ C.gamma (D.gammaIndex d) := by
    intro h
    have hnot := hproper hfGammaNe.symm
      ⟨L.lastInside, hcrossIncident, hfGammaIncident⟩ L.crossingColor
    exact hnot (by simpa [h] using hfGammaColor)
  have hAlpha0Gamma : D.alpha0 ≠ C.gamma (D.gammaIndex d) :=
    D.alpha0_not_block (D.gammaIndex d)
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hy0 : C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈
      TreeSequenceVertexSet T := by
    rw [← C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩]
    simp [TreeSequenceVertexSet]
  have hdcard : 2 ≤
      (BoundaryColorEdges G phi (TreeSequenceVertexSet T) d.1).card := by
    have hd := (Finset.mem_filter.mp d.2).2
    simpa only [DefectiveColor] using hd
  obtain ⟨bDelta, hbDelta⟩ := Finset.card_pos.mp
    (lt_of_lt_of_le Nat.zero_lt_two hdcard)
  have hbDeltaBoundary : bDelta ∈ BoundaryEdges G (TreeSequenceVertexSet T) :=
    (Finset.mem_filter.mp hbDelta).1
  have hbDeltaColor : phi bDelta = some d.1 :=
    (Finset.mem_filter.mp hbDelta).2
  have hAlpha0Delta : D.alpha0 ≠ d.1 := by
    intro h
    have hnot := hclosed hbDeltaBoundary hy0 hbDeltaColor
    exact hnot (by simpa [h] using D.alpha0_missing_at_y0)
  have hGammaDelta : C.gamma (D.gammaIndex d) ≠ d.1 := by
    intro h
    have hmissing := D.gamma_missing_at_v0 d
    have hinc : Incident G (D.v0 d) (D.f0 d) := by
      change D.v0 d ∈ G.ends (D.f0 d)
      rw [D.f0_ends]
      simp
    have hpresent : C.gamma (D.gammaIndex d) ∈
        PresentColors G phi (D.v0 d) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨D.f0 d, hinc, by simpa [h] using D.f0_color d⟩
    exact (Finset.mem_sdiff.mp hmissing).2 hpresent
  have colorFixed (c : Fin k)
      (hcGamma : c ≠ C.gamma (D.gammaIndex d)) (hcDelta : c ≠ d.1)
      (f : E) :
      TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d)) f = some c ↔ phi f = some c := by
    simp only [TwoColorComponentSwap]
    by_cases hf : Sum.inr f ∈ TwoColorComponent G phi
        (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
    · simp only [hf, ite_eq_left]
      by_cases hfg : phi f = some (C.gamma (D.gammaIndex d))
      · rw [hfg]
        simp only [ite_eq_left]
        constructor
        · intro hnew
          exact False.elim (hcDelta (Option.some.inj hnew).symm)
        · intro hold
          exact False.elim (hcGamma (Option.some.inj hold).symm)
      · by_cases hfd : phi f = some d.1
        · rw [hfd]
          simp only [Option.some.injEq, hGammaDelta.symm, ite_false, ite_eq_left]
          constructor
          · intro hnew
            exact False.elim (hcGamma hnew.symm)
          · intro hold
            exact False.elim (hcDelta hold.symm)
        · simp [hfg, hfd]
    · simp [hf]
  have hgraph : TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha := by
    exact @ScheideReplacementConfinement_hgraph_272 V E inferInstance inferInstance inferInstance
        G k e0 phi T C D alpha d hAlphaDelta hAlphaGamma hAlpha0Gamma hAlpha0Delta colorFixed
  have hused := ScheideReplacementUsedWitness G k e0 phi T C D R d
  obtain ⟨hfree, hnondef⟩ :=
    ScheideReplacementExitNotDefective G k e0 phi T C D R alpha L hlast
      d hpair hgraph
  have hprefix := ScheideReplacementPathPrefix G k e0 phi T C D R alpha L
    d hpair hgraph hnondef
  have hboundary := ScheideReplacementBoundaryUnique G k e0 phi T C D R
    alpha L d hprefix
  exact ⟨d, hpair, hgraph, hused, hfree, hnondef, hprefix, hboundary⟩

end GoldbergSeymour

end
