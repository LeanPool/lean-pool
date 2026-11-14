/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideLastExitPath
public import LeanPool.GoldbergSeymour.ScheideReplacementMaximum
public import LeanPool.GoldbergSeymour.ScheideReplacementUsedWitness

/-!
# Scheide Replacement Exit Not Defective

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideReplacementExitNotDefective {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (L : ScheideLastExitPath G k e0 phi T C D R alpha)
    (hlast : L.lastInside ∉ TreeSequenceVertexSet T)
    (d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)})
    (hpair : L.lastInside ∈ ({(R d).u1, (R d).u2} : Finset V))
    (hgraph : TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha) :
    (∃ beta,
      beta ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) L.lastInside ∧
      beta ∈ TreeFreeColors
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) (R d).replacementTree) ∧
    alpha ∉ DefectiveColors G
      (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)))
      (TreeSequenceVertexSet (R d).replacementTree) := by
  classical
  let phiD := TwoColorComponentSwap G phi
    (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  let Td := (R d).replacementTree
  let VT := TreeSequenceVertexSet Td
  let Z := TreeSequenceVertexSet T \
    {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}
  let X := ScheideEnlargedVertexSet R
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hmaximum := ScheideReplacementMaximum G k e0 phi T C D d (R d)
  dsimp at hmaximum
  have hglobal : GlobalMaximumTriple G k e0 phiD Td := by
    simpa [phiD, Td] using hmaximum.2.2
  have horder := ScheideGlobalMaximumOrder G k e0 phiD Td hglobal
  have helementary : ColoredVertexSetElementary G phiD VT := by
    change ColoredVertexSetElementary G phiD (TreeSequenceVertexSet Td)
    exact horder.2.2.2.1
  have hVTsubX : VT ⊆ X := by
    intro v hv
    change v ∈ TreeSequenceVertexSet (R d).replacementTree at hv
    rw [(R d).replacement_vertices] at hv
    unfold X ScheideEnlargedVertexSet
    rw [Finset.mem_union]
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inl (Finset.mem_sdiff.mp hv).1
    · refine Or.inr (Finset.mem_biUnion.mpr ?_)
      exact ⟨d, Finset.mem_univ d, hv⟩
  have hbaseZ : ∀ a : Fin C.p, C.y a ∈ Z := by
    intro a
    have haT : C.y a ∈ TreeSequenceVertexSet T := by
      rw [← C.base_vertex_position a]
      simp [TreeSequenceVertexSet]
    refine Finset.mem_sdiff.mpr ⟨haT, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro heq
    rcases heq with heq | heq
    · have hi := T.vertex_injective (C.base_vertex_position a |>.trans
        (heq ▸ (C.block_vertex_position (D.gammaIndex d) (0 : Fin 2))).symm)
      have hv := congrArg Fin.val hi
      have hp := C.p_ge_two
      have hr := (D.gammaIndex d).isLt
      simp at hv
      omega
    · have hi := T.vertex_injective (C.base_vertex_position a |>.trans
        (heq ▸ (C.block_vertex_position (D.gammaIndex d) (1 : Fin 2))).symm)
      have hv := congrArg Fin.val hi
      have hp := C.p_ge_two
      have hr := (D.gammaIndex d).isLt
      simp at hv
      omega
  have hy0Z : y0 ∈ Z := by
    simpa [y0] using hbaseZ
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0T : y0 ∈ TreeSequenceVertexSet T := by
    exact Finset.mem_sdiff.mp hy0Z |>.1
  have hy0VT : y0 ∈ VT := by
    change y0 ∈ TreeSequenceVertexSet (R d).replacementTree
    rw [(R d).replacement_vertices]
    exact Finset.mem_union_left _ hy0Z
  have hvVT : L.lastInside ∈ VT := by
    change L.lastInside ∈ TreeSequenceVertexSet (R d).replacementTree
    rw [(R d).replacement_vertices]
    exact Finset.mem_union_right _ hpair
  have heffect := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  dsimp at heffect
  have hy0Missing : D.alpha0 ∈ MissingColors G phiD y0 := by
    by_cases heq : y0 = D.v0 d
    · rw [heq]
      change D.alpha0 ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) (D.v0 d)
      rw [heffect.2.2.2.1]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      exact ⟨D.alpha0_not_block (D.gammaIndex d), by
        simpa [y0, heq] using D.alpha0_missing_at_y0⟩
    · change D.alpha0 ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) y0
      rw [heffect.2.2.2.2.2.1 y0 hy0T heq]
      simpa [y0] using D.alpha0_missing_at_y0
  have hmissingNonempty : (MissingColors G phiD L.lastInside).Nonempty := by
    have hcounts := ScheideGlobalMaximumMissingCounts G k e0 phiD Td hglobal
      L.lastInside hvVT
    by_cases hincident : Incident G L.lastInside e0
    · apply Finset.card_pos.mp
      have hcard := (hcounts.1 hincident).2
      omega
    · apply Finset.card_pos.mp
      have hcard := (hcounts.2 hincident).2
      omega
  obtain ⟨beta, hbetaMissing⟩ := hmissingNonempty
  have hbetaUnused : beta ∉ TreeUsedColors phiD Td := by
    intro hused
    have hused' : beta ∈ TreeUsedColors
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d))) (R d).replacementTree := by
      simpa [phiD, Td] using hused
    obtain ⟨z, hzZ, hzMissing⟩ :=
      ScheideReplacementUsedWitness G k e0 phi T C D R d beta hused'
    have hzVT : z ∈ VT := by
      change z ∈ TreeSequenceVertexSet (R d).replacementTree
      rw [(R d).replacement_vertices]
      exact Finset.mem_union_left _ hzZ
    have hzne : z ≠ L.lastInside := by
      intro heq
      exact hlast (heq ▸ (Finset.mem_sdiff.mp hzZ).1)
    have hdisjoint := helementary hzVT hvVT hzne
    exact (Finset.disjoint_left.mp hdisjoint) (by
      simpa [phiD] using hzMissing) hbetaMissing
  have hbetaFree : beta ∈ TreeFreeColors phiD Td := by
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hbetaUnused⟩
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨L.lastInside, hvVT, hbetaMissing⟩
  refine ⟨⟨beta, hbetaMissing, hbetaFree⟩, ?_⟩
  intro halphaDefective
  have hswapGraphs : ∀ (psi : PartialEdgeColoring E k) (a b : Fin k),
      TwoColorIncidenceGraph G psi a b =
        TwoColorIncidenceGraph G psi b a := by
    intro psi a b
    ext x y
    cases x <;> cases y <;>
      simp only [TwoColorIncidenceGraph, and_congr_right_iff]
    all_goals aesop
  have hgivenGraph : TwoColorIncidenceGraph G phiD D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha := by
    simpa [phiD] using hgraph
  have htransportGraph : TwoColorIncidenceGraph G phiD alpha D.alpha0 =
      TwoColorIncidenceGraph G phi D.alpha0 alpha := by
    calc
      TwoColorIncidenceGraph G phiD alpha D.alpha0 =
          TwoColorIncidenceGraph G phiD D.alpha0 alpha :=
        hswapGraphs phiD alpha D.alpha0
      _ = TwoColorIncidenceGraph G phi D.alpha0 alpha := hgivenGraph
  have hgraphLe : TwoColorIncidenceGraph G phi D.alpha0 alpha ≤
      TwoColorIncidenceGraph G phiD alpha D.alpha0 := by
    rw [htransportGraph]
  let pD : (TwoColorIncidenceGraph G phiD alpha D.alpha0).Walk
      (Sum.inl y0) (Sum.inl L.terminal) := L.path.mapLe hgraphLe
  have hpD : ScheideDefectiveChainPath Td phiD alpha D.alpha0
      y0 L.terminal pD := by
    refine ⟨hy0VT, ?_, ?_, ?_⟩
    · simpa [pD] using L.pathSimple
    · intro hterminal
      exact L.terminalOutside (hVTsubX hterminal)
    · have hcomponentEq :
          TwoColorComponent G phiD alpha D.alpha0 (Sum.inl y0) =
            TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0) := by
        unfold TwoColorComponent
        rw [htransportGraph]
      rw [hcomponentEq]
      simpa [pD, y0] using L.pathSpans
  let lastIndexD : Fin (pD.length + 1) := ⟨L.lastIndex.val, by
    simpa [pD] using L.lastIndex.isLt⟩
  have hlastAt : pD.getVert lastIndexD.val = Sum.inl L.lastInside := by
    simpa [pD, lastIndexD] using L.lastInsideAt
  have hafter : ∀ r : Fin (pD.length + 1), lastIndexD.val < r.val →
      ∀ w : V, pD.getVert r.val = Sum.inl w → w ∉ VT := by
    intro r hir w hw
    let rL : Fin (L.path.length + 1) := ⟨r.val, by
      simpa [pD] using r.isLt⟩
    have hirL : L.lastIndex.val < rL.val := by
      simpa [lastIndexD, rL] using hir
    have hwL : L.path.getVert rL.val = Sum.inl w := by
      simpa [pD, rL] using hw
    intro hwVT
    exact (L.afterLastOutside rL hirL w hwL) (hVTsubX hwVT)
  have hexit : ScheideExitVertex Td phiD L.lastInside := by
    refine ⟨y0, D.alpha0, alpha, hy0VT, hy0Missing,
      halphaDefective, L.terminal, pD, hpD, lastIndexD,
      hlastAt, hvVT, ?_⟩
    exact hafter
  have hexitMem : L.lastInside ∈ ScheideExitVertices Td phiD := by
    simpa [ScheideExitVertices] using hexit
  have hnoFree := ScheideExitNoFree G k e0 phiD Td hglobal
    L.lastInside hexitMem
  exact (Finset.disjoint_left.mp hnoFree) hbetaMissing hbetaFree

end GoldbergSeymour

end
