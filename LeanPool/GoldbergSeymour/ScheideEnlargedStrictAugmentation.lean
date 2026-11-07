/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Scheide Enlarged Strict Augmentation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem ScheideEnlargedStrictAugmentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    (∃ (alpha : Fin k)
      (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
      (f : E) (w u : V),
      let phiD := TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
      let Q := TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
      let psi := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)
      alpha ≠ D.alpha0 ∧
        G.ends f = s(w, u) ∧
        phiD f = some alpha ∧
        Sum.inr f ∈ Q ∧
        (∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∉ Q) ∧
        GlobalMaximumTriple G k e0 psi (R d).replacementTree ∧
        D.alpha0 ∈ MissingColors G phiD
          (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩) ∧
        C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈
          TreeSequenceVertexSet (R d).replacementTree ∧
        w ∈ TreeSequenceVertexSet (R d).replacementTree ∧
        u ∉ TreeSequenceVertexSet (R d).replacementTree ∧
        f ∉ Finset.univ.image (R d).replacementTree.edge) →
    ∃ (psi : PartialEdgeColoring E k) (S : TreeSequence G e0),
      KTriple G k e0 psi ∧
        TashkinovTree G e0 psi S ∧
        (TreeSequenceVertexSet S).card = TashkinovOrder G + 1 := by
  classical
  rintro ⟨alpha, d, f, w, u, hpack⟩
  let phiD := TwoColorComponentSwap G phi
    (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  let Q := TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
  let psi := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)
  let Td := (R d).replacementTree
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  change alpha ≠ D.alpha0 ∧
      G.ends f = s(w, u) ∧
      phiD f = some alpha ∧
      Sum.inr f ∈ Q ∧
      (∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∉ Q) ∧
      GlobalMaximumTriple G k e0 psi Td ∧
      D.alpha0 ∈ MissingColors G phiD y0 ∧
      y0 ∈ TreeSequenceVertexSet Td ∧
      w ∈ TreeSequenceVertexSet Td ∧
      u ∉ TreeSequenceVertexSet Td ∧
      f ∉ Finset.univ.image Td.edge at hpack
  rcases hpack with ⟨halpha, hfends, hfcolor, hfQ, hQavoid, hmaximum,
    halpha0Missing, hy0Td, hwTd, huTd, hfFresh⟩
  have hfPsi : psi f = some D.alpha0 := by
    have hfQ' : Sum.inr f ∈
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
      simpa [Q] using hfQ
    simp [psi, TwoColorComponentSwap, hfQ', hfcolor, halpha]
  have hy0T : y0 ∈ TreeSequenceVertexSet T := by
    have hp : (0 : ℕ) < T.length + 1 := by omega
    have hv := C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [y0, TreeSequenceVertexSet] using
      (show ∃ i : Fin (T.length + 1), T.vertex i = y0 from
        ⟨⟨0, hp⟩, by simpa [y0] using hv⟩)
  have hedgeColor : ∀ g : E, Sum.inr g ∈ Q →
      phiD g = some D.alpha0 ∨ phiD g = some alpha := by
    intro g hg
    change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inr g) =
      (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl u) at hg
    have heq := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hg
    have hp : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Reachable
        (Sum.inr g) (Sum.inl u) := SimpleGraph.ConnectedComponent.exact heq
    have hsupp := SimpleGraph.mem_support_of_reachable (by simp) hp
    obtain ⟨z, hz⟩ :=
      ((TwoColorIncidenceGraph G phiD D.alpha0 alpha).mem_support).mp hsupp
    cases z with
    | inl v => exact hz.2
    | inr e => simp [TwoColorIncidenceGraph] at hz
  have hedgeAvoid : ∀ g : E, Incident G y0 g → Sum.inr g ∉ Q := by
    intro g hinc hg
    have hcolor := hedgeColor g hg
    have hadj : (TwoColorIncidenceGraph G phiD D.alpha0 alpha).Adj
        (Sum.inl y0) (Sum.inr g) := by
      simp [TwoColorIncidenceGraph, hinc, hcolor]
    have hc :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    apply hQavoid y0 hy0T
    change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl y0) =
      (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl u)
    change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inr g) =
      (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl u) at hg
    exact hc.trans hg
  have hincidentFixed : ∀ g : E, Incident G y0 g → psi g = phiD g := by
    intro g hinc
    have hg : Sum.inr g ∉
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
      simpa [Q] using hedgeAvoid g hinc
    simp [psi, TwoColorComponentSwap, hg]
  have halpha0MissingPsi : D.alpha0 ∈ MissingColors G psi y0 := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
      at halpha0Missing ⊢
    intro hpresent
    apply halpha0Missing
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hpresent ⊢
    obtain ⟨g, hinc, hg⟩ := hpresent
    refine ⟨g, hinc, ?_⟩
    rw [hincidentFixed g hinc] at hg
    exact hg
  have hfBoundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet Td) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hwTd, u, huTd, hfends⟩
  obtain ⟨S, hTdS⟩ := TreeSequenceBoundaryEdgeAppendExists Td f hfBoundary
  have htreeS : TashkinovTree G e0 psi S := by
    rcases hTdS with ⟨hlen, hinitial, hlast⟩
    rcases hinitial with ⟨hle, hvert, hedge⟩
    intro q hq
    by_cases hold : q.val < Td.length
    · let qTd : Fin Td.length := ⟨q.val, hold⟩
      obtain ⟨a, c, hc, hm⟩ := hmaximum.2.1 qTd
        (by simpa [qTd] using hq)
      let aS : Fin (q.val + 1) := ⟨a.val, by simpa [qTd] using a.isLt⟩
      refine ⟨aS, c, ?_, ?_⟩
      · have hqeq : Fin.castLE hle qTd = q := Fin.ext rfl
        rw [← hqeq, hedge]
        exact hc
      · let oldVertexIndex : Fin (Td.length + 1) :=
          Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ qTd.isLt))
        let newVertexIndex : Fin (S.length + 1) :=
          Fin.castLT aS (Nat.lt_trans aS.isLt (Nat.succ_lt_succ q.isLt))
        have hindex : Fin.castLE (Nat.succ_le_succ hle) oldVertexIndex =
            newVertexIndex := Fin.ext rfl
        have hvertex : S.vertex newVertexIndex = Td.vertex oldVertexIndex := by
          rw [← hindex]
          exact hvert oldVertexIndex
        simpa [oldVertexIndex, newVertexIndex] using hvertex.symm ▸ hm
    · have hqval : q.val = Td.length := by
        have hqbound : q.val < Td.length + 1 := by simpa [hlen] using q.isLt
        omega
      obtain ⟨i, hi⟩ : ∃ i : Fin (Td.length + 1), Td.vertex i = y0 := by
        simpa [TreeSequenceVertexSet] using hy0Td
      let a : Fin (q.val + 1) := ⟨i.val, by omega⟩
      refine ⟨a, D.alpha0, ?_, ?_⟩
      · have hqlast : q = Fin.cast hlen.symm (Fin.last Td.length) := by
          apply Fin.ext
          simpa using hqval
        rw [hqlast, hlast]
        exact hfPsi
      · let newVertexIndex : Fin (S.length + 1) :=
          Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))
        have hindex : Fin.castLE (Nat.succ_le_succ hle) i =
            newVertexIndex := Fin.ext rfl
        have hvertex : S.vertex newVertexIndex = y0 := by
          rw [← hindex, hvert]
          exact hi
        simpa [newVertexIndex, hvertex] using halpha0MissingPsi
  refine ⟨psi, S, hmaximum.1, htreeS, ?_⟩
  have hcardS : (TreeSequenceVertexSet S).card = S.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      S.vertex_injective]
  have hcardTd : (TreeSequenceVertexSet Td).card = Td.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      Td.vertex_injective]
  rw [hcardS, hTdS.1, ← hcardTd, hmaximum.2.2]

end GoldbergSeymour

end
