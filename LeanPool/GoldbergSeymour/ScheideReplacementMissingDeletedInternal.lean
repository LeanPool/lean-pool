/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ClosedSetTwoColorComponentAvoidance
public import LeanPool.GoldbergSeymour.ScheideSymmetricDefectiveInternal

/-!
# Scheide Replacement Missing Deleted Internal

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_hTreePsi_444.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (alpha : Fin k),
    let X : Finset V := TreeSequenceVertexSet T;
    let _ : Fin k := C.gamma (D.gammaIndex d);
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let Z : Finset V := X \ { ug0, ug1 };
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree;
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.alpha0 alpha (Sum.inl ug0);
        (
    ∀ v ∈ XD,
    ∀ (f : E), Incident G v f → psi f = phi f) → (
    ∀ v ∈ XD, MissingColors G psi v = MissingColors G phi v) → (
    ∀ (q : Fin C.p), C.y q ∈ Z) → (
    ∀ v ∈ Z, v ∈ XD) → TashkinovTree G e0 psi T := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R alpha X gamma ug0 ug1 Z XD psi hPsiFixedAt
      hMissingPsiFixed hBaseInZ hZInXD j hj
  by_cases hbase : j.val < C.p - 1
  · obtain ⟨i, c, hedge, hmissing⟩ := C.globally_maximum.2.1 j hj
    let q : Fin C.p := ⟨i.val, by omega⟩
    have hqVertex : T.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) = C.y q := by
      have hind : Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)) =
            ⟨q.val, by
              have hq := q.isLt
              have hl := C.length_eq
              omega⟩ := by
        apply Fin.ext
        rfl
      rw [hind]
      exact C.base_vertex_position q
    let next : Fin C.p := ⟨j.val + 1, by omega⟩
    have hnextZ : C.y next ∈ Z := hBaseInZ next
    have hnextVertex : T.vertex j.succ = C.y next := by
      have hind : j.succ = ⟨next.val, by
          have hn := next.isLt
          have hl := C.length_eq
          omega⟩ := by
        apply Fin.ext
        rfl
      rw [hind]
      exact C.base_vertex_position next
    have hedgeIncident : Incident G (C.y next) (T.edge j) := by
      obtain ⟨r, hr⟩ := T.attaches j
      change C.y next ∈ G.ends (T.edge j)
      rw [hr, hnextVertex]
      simp
    have hedgeFixed := hPsiFixedAt (C.y next) (hZInXD _ hnextZ)
      (T.edge j) hedgeIncident
    refine ⟨i, c, ?_, ?_⟩
    · exact hedgeFixed.trans hedge
    · rw [hMissingPsiFixed _ (by
          rw [hqVertex]
          exact hZInXD _ (hBaseInZ q))]
      exact hmissing
  · let r : Fin C.s := ⟨(j.val - (C.p - 1)) / 2, by
        have hj := j.isLt
        have hi := (D.gammaIndex d).isLt
        have hl := C.length_eq
        omega⟩
    let l : Fin 2 := ⟨(j.val - (C.p - 1)) % 2, Nat.mod_lt _ (by omega)⟩
    have hjDecomp : C.p - 1 + 2 * r.val + l.val = j.val := by
      dsimp [r, l]
      have hmod := Nat.mod_add_div (j.val - (C.p - 1)) 2
      omega
    have hedgeEq : T.edge j = C.blockEdge r l := by
      rw [← C.block_edge_position r l]
      apply congrArg T.edge
      apply Fin.ext
      exact hjDecomp.symm
    obtain ⟨q, hends⟩ := C.block_attaches_to_base r l
    have hqZ : C.y q ∈ Z := hBaseInZ q
    have hinc : Incident G (C.y q) (T.edge j) := by
      change C.y q ∈ G.ends (T.edge j)
      rw [hedgeEq, hends]
      simp []
    have hedgeFixed := hPsiFixedAt (C.y q) (hZInXD _ hqZ) (T.edge j) hinc
    obtain ⟨w, hwMissing⟩ := C.block_color_missing_on_base r
    let i : Fin (j.val + 1) := ⟨w.val, by
      have hw := w.isLt
      omega⟩
    refine ⟨i, C.gamma r, ?_, ?_⟩
    · rw [hedgeFixed, hedgeEq]
      exact C.block_color r l
    · have hvertex : T.vertex (Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) = C.y w := by
        have hind : Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)) =
              ⟨w.val, by
                have hw := w.isLt
                have hl := C.length_eq
                omega⟩ := by
          apply Fin.ext
          rfl
        rw [hind]
        exact C.base_vertex_position w
      rw [hMissingPsiFixed _ (by
        rw [hvertex]
        exact hZInXD _ (hBaseInZ w))]
      rw [hvertex]
      exact hwMissing

private theorem helper_hPairMissingFixed_364.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    ∀ (u : V), u = R.u1 ∨ u = R.u2 → MissingColors G phiD u = MissingColors G phi u := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD u hu
  simp only [MissingColors]
  congr 1
  ext c
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, huf, hfc⟩
    refine ⟨f, huf, ?_⟩
    have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R f (by
      rcases hu with rfl | rfl
      · exact Or.inl huf
      · exact Or.inr huf)
    simpa [phiD, gamma] using hfixed.symm.trans hfc
  · rintro ⟨f, huf, hfc⟩
    refine ⟨f, huf, ?_⟩
    have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R f (by
      rcases hu with rfl | rfl
      · exact Or.inl huf
      · exact Or.inr huf)
    simpa [phiD, gamma] using hfixed.trans hfc

private theorem helper_hBaseInZ_524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (_ : ScheideReplacementData
        G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let Z : Finset V := X \ { ug0, ug1 };
    ∀ (q : Fin C.p), C.y q ∈ Z := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X ug0 ug1 Z q
  have hqX : C.y q ∈ X := by
    change C.y q ∈ TreeSequenceVertexSet T
    rw [← C.base_vertex_position q]
    simp [TreeSequenceVertexSet]
  have hq0 : C.y q ≠ ug0 := by
    intro h
    have hv := (C.base_vertex_position q).trans
      (h.trans (C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)).symm)
    have hi := congrArg Fin.val (T.vertex_injective hv)
    simp at hi
    omega
  have hq1 : C.y q ≠ ug1 := by
    intro h
    have hv := (C.base_vertex_position q).trans
      (h.trans (C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)).symm)
    have hi := congrArg Fin.val (T.vertex_injective hv)
    simp at hi
    omega
  simp [Z, hqX, hq0, hq1]

private theorem helper_hAlphaBoundaryOutside_598.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (alpha : Fin k),
    let X : Finset V := TreeSequenceVertexSet T;
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p); ug0 ∈ X →
        ug1 ∈ X → y0 ∈ X → alpha ≠ D.alpha0 →
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl ug0); Sum.inl ug0 ∈ K →
        Sum.inl ug1 ∈ K →
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.alpha0 alpha (Sum.inl ug0);
        ColoredVertexSetClosed G psi X → D.alpha0 ∈ MissingColors G psi y0 → (
    ∀ (x : V), Sum.inl x ∈ K →
    ∀ (f : E), Incident G x f → phi f = some alpha → Sum.inr f ∈ K) →
    ∀ (x : V), x = ug0 ∨ x = ug1 →
    ∀ (f : E), Incident G x f → phi f = some alpha →
    ∀ (w : V), G.ends f = s(x, w) → w ∉ X → False := by
  classical
  intro V E _ _ _ G k e0 phi T C D d alpha X ug0 ug1 y0 hug0X hug1X hy0X hAlphaNeAlpha0 K hug0K
      hug1K psi hXPsiClosed hAlpha0PsiY0 hAlphaEdgeInK x hx f hxf hcolor w hends hwX
  have hxX : x ∈ X := by
    rcases hx with rfl | rfl
    · exact hug0X
    · exact hug1X
  have hfK : Sum.inr f ∈ K := by
    apply hAlphaEdgeInK x
    · rcases hx with rfl | rfl
      · exact hug0K
      · exact hug1K
    · exact hxf
    · exact hcolor
  have hcolorPsi : psi f = some D.alpha0 := by
    simp [psi, K, TwoColorComponentSwap, hfK, hcolor,
      hAlphaNeAlpha0]
  have hfBoundary : f ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hxX, w, hwX, hends⟩
  exact (hXPsiClosed hfBoundary hy0X hcolorPsi) hAlpha0PsiY0

private theorem helper_hNoIncident_622.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (alpha : Fin k),
    let X : Finset V := TreeSequenceVertexSet T;
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let Z : Finset V := X \ { ug0, ug1 }; (
    ∀ (x : V), x = ug0 ∨ x = ug1 →
    ∀ (f : E), Incident G x f → phi f = some alpha →
    ∀ (w : V), G.ends f = s(x, w) → w ∈ Z → False) → (
    ∀ (x : V), x = ug0 ∨ x = ug1 →
    ∀ (f : E), Incident G x f → phi f = some alpha →
    ∀ (w : V), G.ends f = s(x, w) → w ∉ X → False) → (¬
    ∃ (f : E), phi f = some alpha ∧ G.ends f = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ)))) →
    ∀ (x : V), x = ug0 ∨ x = ug1 →
    ∀ (f : E), Incident G x f → phi f ≠ some alpha := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d alpha X ug0 ug1 Z hAlphaBoundaryZ hAlphaBoundaryOutside
      hnone x hx f hxf hcolor
  obtain ⟨w, hends⟩ := Sym2.mem_iff_exists.mp hxf
  have hwne : w ≠ x := by
    intro h
    apply G.loopless f x
    simpa [h] using hends
  by_cases hwZ : w ∈ Z
  · exact hAlphaBoundaryZ x hx f hxf hcolor w hends hwZ
  by_cases hwX : w ∈ X
  · have hwPair : w = ug0 ∨ w = ug1 := by
      have : w ∈ ({ug0, ug1} : Finset V) := by
        by_contra hp
        exact hwZ (by simp [Z, hwX, hp])
      simpa using this
    have hinterior : G.ends f = s(ug0, ug1) := by
      rcases hx with rfl | rfl <;> rcases hwPair with rfl | rfl
      · exact False.elim (hwne rfl)
      · exact hends
      · simpa [Sym2.eq_swap] using hends
      · exact False.elim (hwne rfl)
    exact hnone ⟨f, hcolor, by simpa [ug0, ug1] using hinterior⟩
  · exact hAlphaBoundaryOutside x hx f hxf hcolor w hends hwX

private theorem helper_hAlphaDelta_420.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (alpha : Fin k), alpha ∈ MissingColors G phi R.u1 ∨ alpha ∈
        MissingColors G phi R.u2 → Incident G R.u1 R.f1 → Incident G R.u2 R.f2 → alpha ≠ (↑d : Fin
        k) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R alpha hAlpha hf1u1 hf2u2 h
  rcases hAlpha with hAlpha | hAlpha
  · have hnot : alpha ∉ PresentColors G phi R.u1 := by
      simpa [MissingColors] using hAlpha
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R.f1, hf1u1, by simpa [h] using R.f1_color⟩
  · have hnot : alpha ∉ PresentColors G phi R.u2 := by
      simpa [MissingColors] using hAlpha
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R.f2, hf2u2, by simpa [h] using R.f2_color⟩

private theorem helper_hAlphaGamma_439.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (alpha : Fin k), alpha ∈ MissingColors G phi R.u1 ∨ alpha ∈
        MissingColors G phi R.u2 →
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    ∀ (fGamma : E), phi fGamma = some (C.gamma (D.gammaIndex d)) → Incident G R.u1 fGamma →
        Incident G R.u2 fGamma → alpha ≠ gamma := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R alpha hAlpha gamma fGamma hfGammaColor hfGammaU1
      hfGammaU2 h
  rcases hAlpha with hAlpha | hAlpha
  · have hnot : alpha ∉ PresentColors G phi R.u1 := by
      simpa [MissingColors] using hAlpha
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fGamma, hfGammaU1, by simpa [gamma, h] using hfGammaColor⟩
  · have hnot : alpha ∉ PresentColors G phi R.u2 := by
      simpa [MissingColors] using hAlpha
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fGamma, hfGammaU2, by simpa [gamma, h] using hfGammaColor⟩

private theorem helper_hPhiDAlpha0_483.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d)); gamma ≠ (↑d : Fin k) → D.alpha0 ≠ gamma → D.alpha0 ≠ (↑d : Fin k) →
    ∀ (f : E), phiD f = some D.alpha0 ↔ phi f = some D.alpha0 := by
  classical
  intro V E _ _ _ G k e0 phi T C D d gamma phiD hGammaDelta hAlpha0Gamma hAlpha0Delta f
  simp only [phiD, TwoColorComponentSwap]
  by_cases hf : Sum.inr f ∈
      TwoColorComponent G phi gamma d.1 (Sum.inl (D.v0 d))
  · by_cases hfg : phi f = some gamma
    · simp only [hf, ite_eq_left, hfg, Option.some.injEq]
      constructor
      · intro h
        exact False.elim (hAlpha0Delta h.symm)
      · intro h
        exact False.elim (hAlpha0Gamma h.symm)
    · by_cases hfd : phi f = some d.1
      · simp [hf, hfd, hGammaDelta.symm, hAlpha0Gamma.symm, hAlpha0Delta.symm]
      · simp [hf, hfg, hfd]
  · simp [hf]

private theorem helper_hPhiDAlpha_500.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (alpha : Fin k),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d)); alpha ≠ (↑d : Fin k) → alpha ≠ gamma → gamma ≠ (↑d : Fin k) →
    ∀ (f : E), phiD f = some alpha ↔ phi f = some alpha := by
  classical
  intro V E _ _ _ G k e0 phi T C D d alpha gamma phiD hAlphaDelta hAlphaGamma hGammaDelta f
  simp only [phiD, TwoColorComponentSwap]
  by_cases hf : Sum.inr f ∈
      TwoColorComponent G phi gamma d.1 (Sum.inl (D.v0 d))
  · by_cases hfg : phi f = some gamma
    · simp only [hf, ite_eq_left, hfg, Option.some.injEq]
      constructor
      · intro h
        exact False.elim (hAlphaDelta h.symm)
      · intro h
        exact False.elim (hAlphaGamma h.symm)
    · by_cases hfd : phi f = some d.1
      · simp [hf, hfd, hGammaDelta.symm, hAlphaGamma.symm, hAlphaDelta.symm]
      · simp [hf, hfg, hfd]
  · simp [hf]

private theorem helper_hAlphaNeAlpha0_546.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (alpha : Fin k),
    let X : Finset V := TreeSequenceVertexSet T;
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree; ColoredVertexSetElementary G
        phiD XD → y0 ∈ X → y0 ∈ XD → R.u1 ∈ XD → R.u2 ∈ XD → alpha ∈ MissingColors G phiD R.u1 ∨
        alpha ∈ MissingColors G phiD R.u2 → D.alpha0 ∈ MissingColors G phiD y0 → alpha ≠ D.alpha0
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R alpha X gamma y0 phiD XD hXDElementary hy0X hy0XD hu1XD
      hu2XD hAlphaD hAlpha0D h
  rcases hAlphaD with hAlphaD | hAlphaD
  · have hyu : y0 ≠ R.u1 := by
      intro hyu
      exact R.u1_outside (hyu ▸ hy0X)
    have hdj := hXDElementary hy0XD hu1XD hyu
    exact (Finset.disjoint_left.mp hdj) hAlpha0D (by simpa [h] using hAlphaD)
  · have hyu : y0 ≠ R.u2 := by
      intro hyu
      exact R.u2_outside (hyu ▸ hy0X)
    have hdj := hXDElementary hy0XD hu2XD hyu
    exact (Finset.disjoint_left.mp hdj) hAlpha0D (by simpa [h] using hAlphaD)

private theorem helper_hAvoid_603.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let phiD : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree;
    TwoColorIncidenceGraph G phiD D.alpha0 alpha =
        TwoColorIncidenceGraph G phi D.alpha0 alpha →
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl ug0);
    ((∀ v ∈ XD, Sum.inl v ∉ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl ug0)) ∧
        ∀ (f : E),
          (∃ v ∈ XD, Incident G v f) →
            Sum.inr f ∉ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl ug0)) →
    (∀ v ∈ XD, Sum.inl v ∉ K) ∧ ∀ (f : E), (∃ v ∈ XD, Incident G v f) → Sum.inr f ∉ K := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R alpha gamma ug0 phiD XD hGraph K hAvoidD
  constructor
  · intro v hv hmem
    apply hAvoidD.1 v hv
    change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl v) =
      (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug0)
    rw [hGraph]
    exact hmem
  · intro f hf hmem
    apply hAvoidD.2 f hf
    change (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inr f) =
      (TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug0)
    rw [hGraph]
    exact hmem

private theorem helper_hOnePsi_628.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (alpha : Fin k),
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)); alpha ≠ D.alpha0 →
    let _ : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl ug0);
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.alpha0 alpha (Sum.inl ug0);
        IsOneEdgeUncolored psi e0 := by
  classical
  intro V E _ _ _ G k e0 phi T C D d alpha ug0 hAlphaNeAlpha0 K psi
  have hOne := C.globally_maximum.1.2.2.2.2
  constructor
  · simp [psi, TwoColorComponentSwap, hOne.1]
  · intro f hf
    obtain ⟨c, hfc⟩ := hOne.2 f hf
    by_cases hmem : Sum.inr f ∈ K
    · by_cases hc0 : c = D.alpha0
      · exact ⟨alpha, by
          simp [psi, TwoColorComponentSwap, K, hmem, hfc, hc0]⟩
      · by_cases hca : c = alpha
        · exact ⟨D.alpha0, by
            simp [psi, TwoColorComponentSwap, K, hmem, hfc, hca,
              hAlphaNeAlpha0]⟩
        · exact ⟨c, by
            simp [psi, TwoColorComponentSwap, K, hmem, hfc, hc0, hca]⟩
    · exact ⟨c, by
        simp [psi, TwoColorComponentSwap, K, hmem, hfc]⟩

private theorem helper_hAlphaBoundaryZ_697.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (alpha : Fin k),
    let X : Finset V := TreeSequenceVertexSet T;
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let Z : Finset V := X \ { ug0, ug1 };
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree; ColoredVertexSetClosed G phiD XD
        → ug1 ∈ X → R.u1 ∈ XD → R.u2 ∈ XD → ug0 ∉ XD → (
    ∀ (f : E), phiD f = some alpha ↔ phi f = some alpha) → alpha ∈ MissingColors G phiD R.u1 ∨
        alpha ∈ MissingColors G phiD R.u2 → (
    ∀ v ∈ Z, v ∈ XD) →
    ∀ (x : V), x = ug0 ∨ x = ug1 →
    ∀ (f : E), Incident G x f → phi f = some alpha →
    ∀ (w : V), G.ends f = s(x, w) → w ∈ Z → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R alpha X gamma ug0 ug1 Z phiD XD hXDClosed hug1X hu1XD
      hu2XD hug0NotXD hPhiDAlpha hAlphaD hZInXD x hx f hxf hcolor w hends hwZ
  have hxNotXD : x ∉ XD := by
    rcases hx with rfl | rfl
    · exact hug0NotXD
    · rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
        R.replacement_vertices]
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_sdiff]
      rintro (⟨-, hpair⟩ | h | h)
      · exact hpair (by simp [ug1])
      · exact R.u1_outside (h ▸ hug1X)
      · exact R.u2_outside (h ▸ hug1X)
  have hfBoundary : f ∈ BoundaryEdges G XD := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hZInXD w hwZ, x, hxNotXD, hends.trans Sym2.eq_swap⟩
  have hcolorD : phiD f = some alpha := (hPhiDAlpha f).mpr hcolor
  rcases hAlphaD with hAlphaD | hAlphaD
  · exact (hXDClosed hfBoundary hu1XD hcolorD) hAlphaD
  · exact (hXDClosed hfBoundary hu2XD hcolorD) hAlphaD

private theorem helper_continuation_705.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (alpha : Fin k),
    let X : Finset V := TreeSequenceVertexSet T;
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let _ : Finset V := X \ { ug0, ug1 };
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree; ColoredVertexSetElementary G phi
        X → ColoredVertexSetClosed G phiD XD → ug0 ∈ X → ug1 ∈ X → ug0 ≠ ug1 → y0 ∈ X → y0 ∈ XD →
        R.u1 ∈ XD → R.u2 ∈ XD → ug0 ∉ XD → (
    ∀ (f : E), phiD f = some alpha ↔ phi f = some alpha) → TwoColorIncidenceGraph G phiD D.alpha0
        alpha = TwoColorIncidenceGraph G phi D.alpha0 alpha → alpha ∈ MissingColors G phiD R.u1 ∨
        alpha ∈ MissingColors G phiD R.u2 → D.alpha0 ∈ MissingColors G phiD y0 → alpha ≠ D.alpha0
        →
    let K : Set (V ⊕ E) := TwoColorComponent G phi D.alpha0 alpha (Sum.inl ug0); Sum.inl ug0 ∈ K →
        Sum.inl ug1 ∈ K →
    ∃ (f : E), phi f = some alpha ∧ G.ends f = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R alpha X gamma ug0 ug1 Z y0 phiD XD hXElementary
      hXDClosed hug0X hug1X hug01 hy0X hy0XD hu1XD hu2XD hug0NotXD hPhiDAlpha hGraph hAlphaD
      hAlpha0D hAlphaNeAlpha0 K hug0K hug1K
  have hAvoidD :
      (∀ v ∈ XD, Sum.inl v ∉
          TwoColorComponent G phiD D.alpha0 alpha (Sum.inl ug0)) ∧
        ∀ f : E, (∃ v ∈ XD, Incident G v f) →
          Sum.inr f ∉
            TwoColorComponent G phiD D.alpha0 alpha (Sum.inl ug0) := by
    rcases hAlphaD with hAlphaD | hAlphaD
    · exact ClosedSetTwoColorComponentAvoidance G phiD D.alpha0 alpha XD
        ug0 y0 R.u1 hXDClosed hug0NotXD hy0XD hu1XD hAlpha0D hAlphaD
    · exact ClosedSetTwoColorComponentAvoidance G phiD D.alpha0 alpha XD
        ug0 y0 R.u2 hXDClosed hug0NotXD hy0XD hu2XD hAlpha0D hAlphaD
  have hAvoid :
      (∀ v ∈ XD, Sum.inl v ∉ K) ∧
        ∀ f : E, (∃ v ∈ XD, Incident G v f) → Sum.inr f ∉ K := by
    exact @helper_hAvoid_603 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D d R alpha hGraph hAvoidD
  let psi := TwoColorComponentSwap G phi D.alpha0 alpha (Sum.inl ug0)
  have hProperPsi : IsProperEdgeColoring G psi := by
    exact TwoColorComponentSwapProper G phi D.alpha0 alpha hAlphaNeAlpha0.symm
      C.globally_maximum.1.2.2.2.1 (Sum.inl ug0)
  have hOnePsi : IsOneEdgeUncolored psi e0 := by
    exact @helper_hOnePsi_628 V E inferInstance inferInstance inferInstance G k e0 phi T C D d
        alpha hAlphaNeAlpha0
  have hPsiFixedAt : ∀ v : V, v ∈ XD →
      ∀ f : E, Incident G v f → psi f = phi f := by
    intro v hv f hvf
    have hnot := hAvoid.2 f ⟨v, hv, hvf⟩
    simp [psi, K, TwoColorComponentSwap, hnot]
  have hMissingPsiFixed : ∀ v : V, v ∈ XD →
      MissingColors G psi v = MissingColors G phi v := by
    intro v hv
    simp only [MissingColors]
    congr 1
    ext c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨f, hvf, hfc⟩
    · exact ⟨f, hvf, (hPsiFixedAt v hv f hvf).symm.trans hfc⟩
    · exact ⟨f, hvf, (hPsiFixedAt v hv f hvf).trans hfc⟩
  have hBaseInZ : ∀ q : Fin C.p, C.y q ∈ Z := by
    exact @helper_hBaseInZ_524 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D d R
  have hZInXD : ∀ v : V, v ∈ Z → v ∈ XD := by
    intro v hv
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    exact Finset.mem_union_left _ (by simpa [X, Z, ug0, ug1] using hv)
  have hTreePsi : TashkinovTree G e0 psi T := by
    exact @helper_hTreePsi_444 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D d R alpha hPsiFixedAt hMissingPsiFixed hBaseInZ hZInXD
  have hGlobalPsi : GlobalMaximumTriple G k e0 psi T := by
    refine ⟨?_, hTreePsi, C.globally_maximum.2.2⟩
    exact ⟨C.globally_maximum.1.1, C.globally_maximum.1.2.1,
      C.globally_maximum.1.2.2.1, hProperPsi, hOnePsi⟩
  have hPsiOrder := ScheideGlobalMaximumOrder G k e0 psi T hGlobalPsi
  have hXPsiClosed : ColoredVertexSetClosed G psi X := by
    change ColoredVertexSetClosed G psi (TreeSequenceVertexSet T)
    exact hPsiOrder.2.2.2.2
  have hAlpha0PsiY0 : D.alpha0 ∈ MissingColors G psi y0 := by
    rw [hMissingPsiFixed y0 hy0XD]
    simpa [y0] using D.alpha0_missing_at_y0
  have hAlphaEdgeInK : ∀ x : V, Sum.inl x ∈ K → ∀ f : E,
      Incident G x f → phi f = some alpha → Sum.inr f ∈ K := by
    intro x hx f hxf hcolor
    change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inr f) =
      (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug0)
    have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
        (Sum.inl x) (Sum.inr f) := by
      simp [TwoColorIncidenceGraph, hxf, hcolor]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hx
  have hAlphaBoundaryZ : ∀ x : V, (x = ug0 ∨ x = ug1) → ∀ f : E,
      Incident G x f → phi f = some alpha →
        ∀ w : V, G.ends f = s(x, w) → w ∈ Z → False := by
    exact @helper_hAlphaBoundaryZ_697 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 phi T C D d R alpha hXDClosed hug1X hu1XD hu2XD hug0NotXD hPhiDAlpha hAlphaD hZInXD
  have hAlphaBoundaryOutside : ∀ x : V, (x = ug0 ∨ x = ug1) → ∀ f : E,
      Incident G x f → phi f = some alpha →
        ∀ w : V, G.ends f = s(x, w) → w ∉ X → False := by
    exact @helper_hAlphaBoundaryOutside_598 V E inferInstance inferInstance inferInstance G k e0
        phi T C D d alpha hug0X hug1X hy0X hAlphaNeAlpha0 hug0K hug1K hXPsiClosed hAlpha0PsiY0
        hAlphaEdgeInK
  by_contra hnone
  have hNoIncident : ∀ x : V, (x = ug0 ∨ x = ug1) →
      ∀ f : E, Incident G x f → phi f ≠ some alpha := by
    exact @helper_hNoIncident_622 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D d alpha hAlphaBoundaryZ hAlphaBoundaryOutside hnone
  have hMissingUg0 : alpha ∈ MissingColors G phi ug0 := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
    obtain ⟨f, hinc, hcolor⟩ := hpresent
    exact hNoIncident ug0 (Or.inl rfl) f hinc hcolor
  have hMissingUg1 : alpha ∈ MissingColors G phi ug1 := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
    obtain ⟨f, hinc, hcolor⟩ := hpresent
    exact hNoIncident ug1 (Or.inr rfl) f hinc hcolor
  have hdj := hXElementary hug0X hug1X hug01
  exact (Finset.disjoint_left.mp hdj) hMissingUg0 hMissingUg1

private theorem helper_continuation_675.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (alpha : Fin k), alpha ∈ MissingColors G phi R.u1 ∨ alpha ∈
        MissingColors G phi R.u2 →
    let X : Finset V := TreeSequenceVertexSet T;
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let Z : Finset V := X \ { ug0, ug1 };
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree; ColoredVertexSetElementary G phi
        X → ColoredVertexSetClosed G phi X → ColoredVertexSetElementary G phiD XD →
        ColoredVertexSetClosed G phiD XD → ug0 ∈ X → ug1 ∈ X → ug0 ≠ ug1 → y0 ∈ X → y0 ∈ Z → y0 ∈
        XD → R.u1 ∈ XD → R.u2 ∈ XD → ug0 ∉ XD → Incident G R.u1 R.f1 → Incident G R.u2 R.f2 →
    ∃ (f : E), phi f = some alpha ∧ G.ends f = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R alpha hAlpha X gamma ug0 ug1 Z y0 phiD XD hXElementary
      hXClosed hXDElementary hXDClosed hug0X hug1X hug01 hy0X hy0Z hy0XD hu1XD hu2XD hug0NotXD
      hf1u1 hf2u2
  have hAlphaDelta : alpha ≠ d.1 := by
    exact @helper_hAlphaDelta_420 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D d R alpha hAlpha hf1u1 hf2u2
  obtain ⟨fGamma, hfGammaColor, hfGammaEnds⟩ :=
    (ScheideSymmetricDefectiveInternal G k e0 phi T C D d R).2
  have hfGammaU1 : Incident G R.u1 fGamma := by
    simp [Incident, hfGammaEnds]
  have hfGammaU2 : Incident G R.u2 fGamma := by
    simp [Incident, hfGammaEnds]
  have hAlphaGamma : alpha ≠ gamma := by
    exact @helper_hAlphaGamma_439 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D d R alpha hAlpha fGamma hfGammaColor hfGammaU1 hfGammaU2
  have hGammaDelta : gamma ≠ d.1 := by
    intro h
    have hnot : gamma ∉ PresentColors G phi (D.v0 d) := by
      simpa [MissingColors, gamma] using D.gamma_missing_at_v0 d
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨D.f0 d, ?_, ?_⟩
    · change D.v0 d ∈ G.ends (D.f0 d)
      rw [D.f0_ends]
      simp []
    · simpa [h] using D.f0_color d
  have hAlpha0Gamma : D.alpha0 ≠ gamma := by
    simpa [gamma] using D.alpha0_not_block (D.gammaIndex d)
  have hDeltaBoundary : ∃ f : E,
      f ∈ BoundaryEdges G X ∧ phi f = some d.1 := by
    have hdcard : 2 ≤ (BoundaryColorEdges G phi X d.1).card := by
      have hd := (Finset.mem_filter.mp d.2).2
      simpa [DefectiveColor, X] using hd
    have hdnonempty : (BoundaryColorEdges G phi X d.1).Nonempty :=
      Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hdcard)
    obtain ⟨f, hf⟩ := hdnonempty
    exact ⟨f, (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
  obtain ⟨fDelta, hfDeltaBoundary, hfDeltaColor⟩ := hDeltaBoundary
  have hDeltaNotMissingY0 : d.1 ∉ MissingColors G phi y0 :=
    hXClosed hfDeltaBoundary hy0X hfDeltaColor
  have hAlpha0Delta : D.alpha0 ≠ d.1 := by
    intro h
    apply hDeltaNotMissingY0
    simpa [y0, h] using D.alpha0_missing_at_y0
  have hPhiDAlpha0 : ∀ f : E,
      phiD f = some D.alpha0 ↔ phi f = some D.alpha0 := by
    exact @helper_hPhiDAlpha0_483 V E inferInstance inferInstance inferInstance G k e0 phi T C D
        d hGammaDelta hAlpha0Gamma hAlpha0Delta
  have hPhiDAlpha : ∀ f : E,
      phiD f = some alpha ↔ phi f = some alpha := by
    exact @helper_hPhiDAlpha_500 V E inferInstance inferInstance inferInstance G k e0 phi T C D d
        alpha hAlphaDelta hAlphaGamma hGammaDelta
  have hGraph : TwoColorIncidenceGraph G phiD D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha := by
    ext x z
    cases x <;> cases z <;>
      simp [TwoColorIncidenceGraph, hPhiDAlpha0, hPhiDAlpha]
  have hPairMissingFixed :
    ∀ u : V, (u = R.u1 ∨ u = R.u2) → MissingColors G phiD u = MissingColors G phi u := by
    exact @helper_hPairMissingFixed_364 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 phi T C D d R
  have hAlphaD :
      alpha ∈ MissingColors G phiD R.u1 ∨
        alpha ∈ MissingColors G phiD R.u2 := by
    rcases hAlpha with hAlpha | hAlpha
    · exact Or.inl (by
        rw [hPairMissingFixed R.u1 (Or.inl rfl)]
        exact hAlpha)
    · exact Or.inr (by
        rw [hPairMissingFixed R.u2 (Or.inr rfl)]
        exact hAlpha)
  have hAlpha0D : D.alpha0 ∈ MissingColors G phiD y0 := by
    have hOld := D.alpha0_missing_at_y0
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and] at hOld ⊢
    intro hpresent
    apply hOld
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hpresent ⊢
    obtain ⟨f, hyf, hfc⟩ := hpresent
    exact ⟨f, hyf, (hPhiDAlpha0 f).mp hfc⟩
  have hAlphaNeAlpha0 : alpha ≠ D.alpha0 := by
    exact @helper_hAlphaNeAlpha0_546 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 phi T C D d R alpha hXDElementary hy0X hy0XD hu1XD hu2XD hAlphaD hAlpha0D
  obtain ⟨fAlpha0, hfAlpha0Color, hfAlpha0Ends⟩ :=
    ScheideStructuralInternalPair G k e0 phi T C (D.gammaIndex d) D.alpha0
      (by simpa [gamma] using hAlpha0Gamma)
      ⟨y0, by simpa [X, Z, ug0, ug1] using hy0Z,
        by simpa [y0] using D.alpha0_missing_at_y0⟩
  let K := TwoColorComponent G phi D.alpha0 alpha (Sum.inl ug0)
  have hug0K : Sum.inl ug0 ∈ K := by
    rfl
  have hfAlpha0Ug0 : Incident G ug0 fAlpha0 := by
    simp [Incident, hfAlpha0Ends, ug0]
  have hfAlpha0Ug1 : Incident G ug1 fAlpha0 := by
    simp [Incident, hfAlpha0Ends, ug1]
  have hfAlpha0K : Sum.inr fAlpha0 ∈ K := by
    change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inr fAlpha0) =
      (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug0)
    have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
        (Sum.inl ug0) (Sum.inr fAlpha0) := by
      simp [TwoColorIncidenceGraph, hfAlpha0Ug0, hfAlpha0Color]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hug1K : Sum.inl ug1 ∈ K := by
    change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug1) =
      (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl ug0)
    have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
        (Sum.inl ug1) (Sum.inr fAlpha0) := by
      simp [TwoColorIncidenceGraph, hfAlpha0Ug1, hfAlpha0Color]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans
      hfAlpha0K
  exact @helper_continuation_705 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R alpha hXElementary hXDClosed hug0X hug1X hug01 hy0X hy0XD hu1XD hu2XD
      hug0NotXD hPhiDAlpha hGraph hAlphaD hAlpha0D hAlphaNeAlpha0 hug0K hug1K
theorem ScheideReplacementMissingDeletedInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k, (alpha ∈ MissingColors G phi R.u1 ∨ alpha ∈ MissingColors G phi R.u2) →
    ∃ f : E, phi f = some alpha ∧ G.ends f = s(C.blockVertex (D.gammaIndex d) 0, C.blockVertex
        (D.gammaIndex d) 1) := by
  classical
  intro alpha hAlpha
  let X := TreeSequenceVertexSet T
  let gamma := C.gamma (D.gammaIndex d)
  let ug0 := C.blockVertex (D.gammaIndex d) 0
  let ug1 := C.blockVertex (D.gammaIndex d) 1
  let Z := X \ {ug0, ug1}
  let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let XD := TreeSequenceVertexSet R.replacementTree
  have hOriginalOrder :=
    ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hXElementary : ColoredVertexSetElementary G phi X := by
    change ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)
    exact hOriginalOrder.2.2.2.1
  have hXClosed : ColoredVertexSetClosed G phi X := by
    change ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)
    exact hOriginalOrder.2.2.2.2
  have hReplacementMaximum :=
    ScheideReplacementMaximum G k e0 phi T C D d R
  have hReplacementGlobal : GlobalMaximumTriple G k e0 phiD R.replacementTree := by
    simpa [phiD, gamma] using hReplacementMaximum.2.2
  have hReplacementOrder :=
    ScheideGlobalMaximumOrder G k e0 phiD R.replacementTree hReplacementGlobal
  have hXDElementary : ColoredVertexSetElementary G phiD XD := by
    change ColoredVertexSetElementary G phiD
      (TreeSequenceVertexSet R.replacementTree)
    exact hReplacementOrder.2.2.2.1
  have hXDClosed : ColoredVertexSetClosed G phiD XD := by
    change ColoredVertexSetClosed G phiD
      (TreeSequenceVertexSet R.replacementTree)
    exact hReplacementOrder.2.2.2.2
  have hug0X : ug0 ∈ X := by
    change C.blockVertex (D.gammaIndex d) 0 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hug1X : ug1 ∈ X := by
    change C.blockVertex (D.gammaIndex d) 1 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hug01 : ug0 ≠ ug1 := by
    intro h
    have hv :=
      (C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)).trans
        (h.trans (C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)).symm)
    have hi := congrArg Fin.val (T.vertex_injective hv)
    simp at hi
  have hy0X : y0 ∈ X := by
    change C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈
      TreeSequenceVertexSet T
    rw [← C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩]
    simp [TreeSequenceVertexSet]
  have hy0ne0 : y0 ≠ ug0 := by
    intro h
    have hv :=
      (C.base_vertex_position
        ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩).trans
        (h.trans (C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)).symm)
    have hi := congrArg Fin.val (T.vertex_injective hv)
    simp at hi
    have hp := C.p_ge_two
    omega
  have hy0ne1 : y0 ≠ ug1 := by
    intro h
    have hv :=
      (C.base_vertex_position
        ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩).trans
        (h.trans (C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)).symm)
    have hi := congrArg Fin.val (T.vertex_injective hv)
    simp at hi
  have hy0Z : y0 ∈ Z := by
    simp [Z, hy0X, hy0ne0, hy0ne1]
  have hy0XD : y0 ∈ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    exact Finset.mem_union_left _ (by simpa [X, Z, ug0, ug1] using hy0Z)
  have hu1XD : R.u1 ∈ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    simp
  have hu2XD : R.u2 ∈ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    simp
  have hug0NotXD : ug0 ∉ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_sdiff]
    rintro (⟨-, hpair⟩ | h | h)
    · exact hpair (by simp [ug0])
    · exact R.u1_outside (h ▸ hug0X)
    · exact R.u2_outside (h ▸ hug0X)
  have hf1u1 : Incident G R.u1 R.f1 := by
    change R.u1 ∈ G.ends R.f1
    rw [R.f1_ends]
    simp []
  have hf2u2 : Incident G R.u2 R.f2 := by
    change R.u2 ∈ G.ends R.f2
    rw [R.f2_ends]
    simp []
  exact @helper_continuation_675 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R alpha hAlpha hXElementary hXClosed hXDElementary hXDClosed hug0X hug1X
      hug01 hy0X hy0Z hy0XD hu1XD hu2XD hug0NotXD hf1u1 hf2u2
end GoldbergSeymour

end
