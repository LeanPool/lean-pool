/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.DefectiveColor
public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.FixedPairMaximalTashkinovTree
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveDeletedTreePair
public import LeanPool.GoldbergSeymour.ScheideDefectiveReturnData
public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideDefectiveSecondTerminalComponent
public import LeanPool.GoldbergSeymour.ScheideDefectiveTerminalComponent
public import LeanPool.GoldbergSeymour.ScheideDefectiveThirdBoundaryEdge
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumFixedPairMaximal
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralExitsInBase
public import LeanPool.GoldbergSeymour.TashkinovOrder
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper

/-!
# Scheide Defective Return Contradiction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation291Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
   (D : ScheideDefectiveSetup G k e0 phi T C)
   (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
   (R : ScheideDefectiveReturnData G k e0 phi T C D d),
   let X : Finset V := TreeSequenceVertexSet T;
   let i : Fin C.s := D.gammaIndex d;
   let j : Fin C.s := R.blockIndex;
   let gamma : Fin k := C.gamma i;
   let gammaJ : Fin k := C.gamma j;
   let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
   let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
   let _ : PartialEdgeColoring E k :=
    TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
   let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
   let _ : Set (V ⊕ E) := TwoColorComponent G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
   let _ : PartialEdgeColoring E k :=
    TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
   let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
   let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
   IsProperEdgeColoring G (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) →
    IsOneEdgeUncolored (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) e0 →
     StableColoring T ∅ phi (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) →
      IsProperEdgeColoring G
        (TwoColorComponentSwap G
         (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex))
         (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) →
       IsOneEdgeUncolored
         (TwoColorComponentSwap G
          (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex))
          (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1))
         e0 →
        (↑d : Fin k) ∈
          MissingColors G
           (TwoColorComponentSwap G
            (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex))
            (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1))
           R.v1 →
         ∀ (Sgamma SgammaJ : TreeSequence G e0),
          TashkinovTree G e0
            (TwoColorComponentSwap G
             (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)))
             (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
            Sgamma →
           TreeSequenceVertexSet Sgamma =
             TreeSequenceVertexSet T \
               {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
                C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪
              { R.u1 } →
            TashkinovTree G e0
              (TwoColorComponentSwap G
               (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex))
               (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1))
              SgammaJ →
             TreeSequenceVertexSet SgammaJ =
               TreeSequenceVertexSet T \
                 {C.blockVertex R.blockIndex (0 : Fin (2 : ℕ)),
                  C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))} ∪
                {D.u0 d} →
              ∀ (f2 : E) (z2 u2 : V),
               G.ends f2 = s(z2, u2) →
                z2 ∈
                  TreeSequenceVertexSet T \
                   ({C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
                     C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪
                    {C.blockVertex R.blockIndex (0 : Fin (2 : ℕ)),
                     C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))}) →
                 u2 ∉ TreeSequenceVertexSet T →
                  TwoColorComponentSwap G
                     (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)))
                     (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f2 =
                    some (↑d : Fin k) →
                   TwoColorComponentSwap G
                      (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex))
                      (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1) f2 =
                     some (↑d : Fin k) →
                    u2 ≠ D.u0 d →
                     u2 ≠ R.u1 →
                      T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s →
                       (∀ (a : Fin C.p) (r : Fin C.s) (b : Fin (2 : ℕ)),
                         C.y a ≠ C.blockVertex r b) →
                        Ui ⊆ X →
                         Uj ⊆ X →
                          Ui.card = (2 : ℕ) →
                           Uj.card = (2 : ℕ) →
                            (∀ (rho : PartialEdgeColoring E k) (S U : TreeSequence G e0) (f : E),
                              TreeSequenceAdjoinEdge S f U →
                               TashkinovTree G e0 rho S →
                                ∀ (c : Fin k),
                                 rho f = some c →
                                  ∀ v ∈ TreeSequenceVertexSet S,
                                   c ∈ MissingColors G rho v → TashkinovTree G e0 rho U) →
                             False

private theorem helper_tashkinov_adjoin_165.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (_ : ScheideDefectiveReturnData G k e0 phi T C D d) (rho : PartialEdgeColoring E k)
      (S U : TreeSequence G e0) (f : E),
    TreeSequenceAdjoinEdge S f U →
    TashkinovTree G e0 rho S →
    ∀ (c : Fin k),
    rho f = some c →
    ∀ v ∈ TreeSequenceVertexSet S,
    c ∈ MissingColors G rho v →
    TashkinovTree G e0 rho U := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R rho S U f hadjoin hS c hf v hv hmiss
  rcases hadjoin with ⟨hlen, hinitial, hlast⟩
  rcases hinitial with ⟨hle, hvert, hedge⟩
  intro q hq
  by_cases hold : q.val < S.length
  · let qS : Fin S.length := ⟨q.val, hold⟩
    obtain ⟨a, color, hcolor, hcolorMissing⟩ :=
      hS qS (by simpa [qS] using hq)
    let aU : Fin (q.val + 1) := ⟨a.val, by simpa [qS] using a.isLt⟩
    refine ⟨aU, color, ?_, ?_⟩
    · have hqeq : Fin.castLE hle qS = q := by
        apply Fin.ext
        rfl
      have hUedge : U.edge q = S.edge qS := by
        rw [← hqeq]
        exact hedge qS
      rw [hUedge]
      exact hcolor
    · let oldVertexIndex : Fin (S.length + 1) :=
        Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ qS.isLt))
      let newVertexIndex : Fin (U.length + 1) :=
        Fin.castLT aU (Nat.lt_trans aU.isLt (Nat.succ_lt_succ q.isLt))
      have hindex : Fin.castLE (Nat.succ_le_succ hle) oldVertexIndex =
          newVertexIndex := by
        apply Fin.ext
        rfl
      have hvertex : U.vertex newVertexIndex = S.vertex oldVertexIndex := by
        rw [← hindex]
        exact hvert oldVertexIndex
      simpa [oldVertexIndex, newVertexIndex] using
        hvertex.symm ▸ hcolorMissing
  · have hqval : q.val = S.length := by
      have hqbound : q.val < S.length + 1 := by simpa [hlen] using q.isLt
      omega
    obtain ⟨a, ha⟩ : ∃ a : Fin (S.length + 1), S.vertex a = v := by
      simpa [TreeSequenceVertexSet] using hv
    let aU : Fin (q.val + 1) := ⟨a.val, by simpa [hqval] using a.isLt⟩
    refine ⟨aU, c, ?_, ?_⟩
    · have hqlast : q = Fin.cast hlen.symm (Fin.last S.length) := by
        apply Fin.ext
        simpa using hqval
      rw [hqlast, hlast]
      exact hf
    · let newVertexIndex : Fin (U.length + 1) :=
        Fin.castLT aU (Nat.lt_trans aU.isLt (Nat.succ_lt_succ q.isLt))
      have hindex : Fin.castLE (Nat.succ_le_succ hle) a =
          newVertexIndex := by
        apply Fin.ext
        rfl
      have hvertex : U.vertex newVertexIndex = v := by
        rw [← hindex, hvert a, ha]
      simpa [newVertexIndex, hvertex] using hmiss

private theorem helper_adjoin_vertex_set_223.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] (G : LooplessMultigraph V E) (e0 : E)
      (A B : TreeSequence G e0) (f : E) (x y : V),
    G.ends f = s(x, y) →
    y ∉ TreeSequenceVertexSet A →
    TreeSequenceAdjoinEdge A f B →
    TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A) := by
  classical
  intro V E _ G e0 A B f x y hxy hyA hAB
  rcases hAB with ⟨hlen, hinit, hlast⟩
  rcases hinit with ⟨hle, hvertices, hedges⟩
  have holdSubset : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨q, hq⟩ := hv
    refine ⟨Fin.castLE (Nat.succ_le_succ hle) q, ?_⟩
    rw [hvertices]
    exact hq
  have hyB : y ∈ TreeSequenceVertexSet B := by
    let q : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
    obtain ⟨a, ha⟩ := B.attaches q
    have hyEnds : y ∈ G.ends (B.edge q) := by
      rw [hlast, hxy]
      simp
    rw [ha] at hyEnds
    rcases (by simpa only [Sym2.mem_iff] using hyEnds) with hynew | hyold
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨q.succ, hynew.symm⟩
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨Fin.castLT a (Nat.lt_trans a.isLt
        (Nat.succ_lt_succ q.isLt)), hyold.symm⟩
  have hinsert : insert y (TreeSequenceVertexSet A) ⊆
      TreeSequenceVertexSet B := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact hyB
    · exact holdSubset hv
  have hAcard : (TreeSequenceVertexSet A).card = A.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      A.vertex_injective]
  have hBcard : (TreeSequenceVertexSet B).card = B.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      B.vertex_injective]
  have hcard : (TreeSequenceVertexSet B).card ≤
      (insert y (TreeSequenceVertexSet A)).card := by
    rw [hBcard, Finset.card_insert_of_notMem hyA, hAcard, hlen]
  exact (Finset.eq_of_subset_of_card_le hinsert hcard).symm

private theorem helper_hone2_388.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let phi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    IsOneEdgeUncolored (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) e0 →
    IsOneEdgeUncolored phi2 e0 := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i gamma phi1 K phi2 hone1
  have hone1' : IsOneEdgeUncolored phi1 e0 := by
    simpa [phi1, gamma, i] using hone1
  constructor
  · simp [phi2, TwoColorComponentSwap, hone1'.1]
  · intro f hfe
    obtain ⟨c, hc⟩ := hone1'.2 f hfe
    by_cases hfK' : Sum.inr f ∈ K
    · by_cases hcg : phi1 f = some gamma
      · exact ⟨d.1, by simp [phi2, TwoColorComponentSwap, K, hfK', hcg]⟩
      · by_cases hcd : phi1 f = some d.1
        · exact ⟨gamma, by simp [phi2, TwoColorComponentSwap, K, hfK',
            hcd]⟩
        · exact ⟨c, by simpa [phi2, TwoColorComponentSwap, K, hfK',
            hcg, hcd] using hc⟩
    · exact ⟨c, by simpa [phi2, TwoColorComponentSwap, K, hfK'] using hc⟩

private theorem helper_hy01_441.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (_ : ScheideDefectiveReturnData G k e0 phi T C D d) (_ _ : TreeSequence G e0),
    T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s →
    ∀ (_ _ : TreeSequence G e0),
    let b0 : Fin C.p := (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let b1 : Fin C.p := (⟨(1 : ℕ), C.p_ge_two⟩ : Fin C.p);
    let y0 : V := C.y b0;
    let y1 : V := C.y b1;
    y0 ≠ y1 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R Sgamma SgammaJ hlength Tgamma TgammaJ b0 b1 y0 y1 h
  let q0 : Fin (T.length + 1) := ⟨0, by omega⟩
  let q1 : Fin (T.length + 1) := ⟨1, by
    have hp := C.p_ge_two
    omega⟩
  have hp0 : T.vertex q0 = y0 := by
    simpa [q0, y0, b0] using C.base_vertex_position b0
  have hp1 : T.vertex q1 = y1 := by
    simpa [q1, y1, b1] using C.base_vertex_position b1
  have hv : T.vertex q0 = T.vertex q1 := hp0.trans (h.trans hp1.symm)
  have hi := congrArg Fin.val (T.vertex_injective hv)
  simp [q0, q1] at hi

private theorem helper_he0ends_454.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (_ : ScheideDefectiveReturnData G k e0 phi T C D d) (_ _ : TreeSequence G e0),
    T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s →
    ∀ (_ _ : TreeSequence G e0),
    let b0 : Fin C.p := (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let b1 : Fin C.p := (⟨(1 : ℕ), C.p_ge_two⟩ : Fin C.p);
    let y0 : V := C.y b0;
    let y1 : V := C.y b1;
    G.ends e0 = s(y1, y0) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R Sgamma SgammaJ hlength Tgamma TgammaJ b0 b1 y0 y1
  let q : Fin T.length := ⟨0, T.positive⟩
  obtain ⟨a, ha⟩ := T.attaches q
  have hfirst : T.edge q = e0 := by simpa [q] using T.first_edge
  have hnew : T.vertex q.succ = y1 := by
    simpa [q, y1, b1] using C.base_vertex_position b1
  have hold : T.vertex (Fin.castLT a
      (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))) = y0 := by
    have hind : Fin.castLT a
        (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)) =
        (⟨0, by omega⟩ : Fin (T.length + 1)) := by
      apply Fin.ext
      simp
    rw [hind]
    simpa [y0, b0] using C.base_vertex_position b0
  rw [← hfirst, ha, hnew, hold]

private theorem helper_hbetaDelta_528.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (_ : ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (_ _ _ _ : TreeSequence G e0),
    ColoredVertexSetClosed G phi X →
    let b0 : Fin C.p := (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let b1 : Fin C.p := (⟨(1 : ℕ), C.p_ge_two⟩ : Fin C.p);
    let y0 : V := C.y b0;
    let y1 : V := C.y b1;
    let M0 : Finset (Fin k) := MissingColors G phi y0;
    ∀ (beta : Fin k),
    let ybeta : V := if beta ∈ M0 then y0 else y1;
    beta ∈ MissingColors G phi ybeta →
    ybeta ∈ X →
    beta ≠ (↑d : Fin k) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X Sgamma SgammaJ Tgamma TgammaJ hclosed0 b0 b1 y0 y1 M0
      beta ybeta hybetaMissing hybetaX hbd
  have hdefective : DefectiveColor G phi X d.1 := by
    exact (Finset.mem_filter.mp d.2).2
  have hboundaryNonempty :
      (BoundaryColorEdges G phi X d.1).Nonempty := by
    apply Finset.card_pos.mp
    unfold DefectiveColor at hdefective
    omega
  obtain ⟨fd, hfd⟩ := hboundaryNonempty
  have hfdBoundary : fd ∈ BoundaryEdges G X :=
    (Finset.mem_filter.mp hfd).1
  have hfdColor : phi fd = some d.1 :=
    (Finset.mem_filter.mp hfd).2
  exact hclosed0 hfdBoundary hybetaX hfdColor (hbd ▸ hybetaMissing)

private theorem helper_hphi2Beta_559.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let phi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ (beta : Fin k),
    gamma ≠ (↑d : Fin k) →
    gamma ≠ beta →
    (↑d : Fin k) ≠ beta →
    (∀ (e : E), phi1 e = some beta ↔ phi e = some beta) →
    ∀ (e : E),
    phi2 e = some beta ↔ phi e = some beta := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i gamma phi1 K phi2 beta hgammaDelta hgammaBeta hdeltaBeta
      hphi1Beta e
  by_cases heK : Sum.inr e ∈ K
  · rw [← hphi1Beta e]
    by_cases heg : phi1 e = some gamma
    · rw [heg]
      simp [phi2, TwoColorComponentSwap, K, heK, heg, hgammaBeta, hdeltaBeta]
    · by_cases hed : phi1 e = some d.1
      · rw [hed]
        simp [phi2, TwoColorComponentSwap, K, heK, hed, hgammaDelta.symm, hgammaBeta, hdeltaBeta]
      · simp [phi2, TwoColorComponentSwap, K, heK, heg, hed]
  · rw [← hphi1Beta e]
    simp [phi2, TwoColorComponentSwap, K, heK]

private theorem helper_hpsi2Beta_583.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideDefectiveReturnData G k e0 phi T C D d),
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let gamma : Fin k := C.gamma i;
    let gammaJ : Fin k := C.gamma j;
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let _ : Set (V ⊕ E) := TwoColorComponent G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    let psi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    ∀ (beta : Fin k),
    gammaJ ≠ (↑d : Fin k) →
    gammaJ ≠ beta →
    (↑d : Fin k) ≠ beta →
    (∀ (e : E), psi1 e = some beta ↔ phi e = some beta) →
    ∀ (e : E),
    psi2 e = some beta ↔ phi e = some beta := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R i j gamma gammaJ psi1 KJ psi2 beta hgammaJDelta
      hgammaJBeta hdeltaBeta hpsi1Beta e
  by_cases heK : Sum.inr e ∈ KJ
  · rw [← hpsi1Beta e]
    by_cases hegJ : psi1 e = some gammaJ
    · rw [hegJ]
      simp [psi2, TwoColorComponentSwap, KJ, heK, hegJ, hgammaJBeta, hdeltaBeta]
    · by_cases hed : psi1 e = some d.1
      · rw [hed]
        simp [psi2, TwoColorComponentSwap, KJ, heK, hed, hgammaJDelta.symm, hgammaJBeta, hdeltaBeta]
      · simp [psi2, TwoColorComponentSwap, KJ, heK, hegJ, hed]
  · rw [← hpsi1Beta e]
    simp [psi2, TwoColorComponentSwap, KJ, heK]

private theorem helper_hu1u0_688.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideDefectiveReturnData G k e0 phi T C D d),
    R.u1 ≠ D.u0 d := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R hout
  have hedge : R.f1 ≠ D.f0 d := by
    intro heq
    have hends : s(R.v1, R.u1) = s(D.v0 d, D.u0 d) := by
      rw [← R.f1_ends, heq, D.f0_ends]
    rcases Sym2.eq_iff.mp hends with hdirect | hcross
    · exact R.v1_ne_v0 hdirect.1
    · exact D.u0_outside d (hcross.1 ▸ R.v1_mem)
  have hadj : AdjacentEdges G R.f1 (D.f0 d) := by
    refine ⟨R.u1, ?_, ?_⟩
    · simp [Incident, R.f1_ends]
    · simp [Incident, D.f0_ends, hout]
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  exact hproper hedge hadj R.f1_color (D.f0_color d)

private theorem helper_continuation_559.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let gamma : Fin k := C.gamma i;
    let gammaJ : Fin k := C.gamma j;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let phi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let psi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    ∀ (Sgamma SgammaJ : TreeSequence G e0),
    TreeSequenceVertexSet Sgamma =
        TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
              C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪
          { R.u1 } →
    TreeSequenceVertexSet SgammaJ =
        TreeSequenceVertexSet T \
            {C.blockVertex R.blockIndex (0 : Fin (2 : ℕ)),
              C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))} ∪
          {D.u0 d} →
    ∀ u2 ∉ TreeSequenceVertexSet T,
    u2 ≠ R.u1 →
    (∀ (rho : PartialEdgeColoring E k) (S U : TreeSequence G e0) (f : E),
        TreeSequenceAdjoinEdge S f U →
          TashkinovTree G e0 rho S →
            ∀ (c : Fin k),
              rho f = some c →
                ∀ v ∈ TreeSequenceVertexSet S,
                  c ∈ MissingColors G rho v → TashkinovTree G e0 rho U) →
    (∀ (A B : TreeSequence G e0) (f : E) (x y : V),
        G.ends f = s(x, y) →
          x ∈ TreeSequenceVertexSet A →
            y ∉ TreeSequenceVertexSet A →
              TreeSequenceAdjoinEdge A f B →
                TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A)) →
    ∀ (Tgamma TgammaJ : TreeSequence G e0),
    TashkinovTree G e0 psi2 TgammaJ →
    TreeSequenceVertexSet Tgamma = insert u2 (TreeSequenceVertexSet Sgamma) →
    TreeSequenceVertexSet TgammaJ = insert u2 (TreeSequenceVertexSet SgammaJ) →
    GlobalMaximumTriple G k e0 psi2 TgammaJ →
    ColoredVertexSetClosed G phi X →
    ColoredVertexSetClosed G phi2 (TreeSequenceVertexSet Tgamma) →
    let b0 : Fin C.p := (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let b1 : Fin C.p := (⟨(1 : ℕ), C.p_ge_two⟩ : Fin C.p);
    let y0 : V := C.y b0;
    let y1 : V := C.y b1;
    let M0 : Finset (Fin k) := MissingColors G phi y0;
    ∀ (beta : Fin k),
    let ybeta : V := if beta ∈ M0 then y0 else y1;
    beta ∈ MissingColors G phi ybeta →
    ybeta ∈ X →
    (∀ (e : E), phi2 e = some beta ↔ phi e = some beta) →
    (∀ (e : E), psi2 e = some beta ↔ phi e = some beta) →
    beta ∈ MissingColors G phi2 ybeta →
    beta ∈ MissingColors G psi2 ybeta →
    ybeta ∈ TreeSequenceVertexSet Tgamma →
    ybeta ∈ TreeSequenceVertexSet TgammaJ →
    u2 ∈ TreeSequenceVertexSet Tgamma →
    u2 ∈ TreeSequenceVertexSet TgammaJ →
    beta ∉ MissingColors G phi2 u2 →
    False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ phi1 phi2 psi1 psi2 Sgamma SgammaJ
      hSgammaVertices hSgammaJVertices u2 hu2X hu2u1 tashkinov_adjoin adjoin_vertex_set Tgamma
      TgammaJ hTgammaJTash hTgammaVertices hTgammaJVertices hglobalJ2 hclosed0 hclosed2 b0 b1 y0
      y1 M0 beta ybeta hybetaMissing hybetaX hphi2Beta hpsi2Beta hybetaMissing2 hybetaMissingJ2
      hybetaTgamma hybetaTgammaJ hu2Tgamma hu2TgammaJ hbetaNotMissingU2
  have hbetaPresentU2 : beta ∈ PresentColors G phi2 u2 := by
    by_contra hnot
    exact hbetaNotMissingU2 (by simp [MissingColors, hnot])
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hbetaPresentU2
  obtain ⟨b, hbu2, hbcolor2⟩ := hbetaPresentU2
  obtain ⟨w, hbends⟩ := Sym2.mem_iff_exists.mp hbu2
  have hwu2 : w ≠ u2 := by
    intro h
    apply G.loopless b u2
    rw [hbends, h]
  have hwTgamma : w ∈ TreeSequenceVertexSet Tgamma := by
    by_contra hw
    have hbBoundary : b ∈ BoundaryEdges G
        (TreeSequenceVertexSet Tgamma) := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u2, hu2Tgamma, w, hw, hbends⟩
    exact hclosed2 hbBoundary hybetaTgamma hbcolor2 hybetaMissing2
  have hbcolor : phi b = some beta := (hphi2Beta b).mp hbcolor2
  have hwNotX : w ∉ X := by
    intro hwX
    have hbBoundary : b ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hwX, u2, hu2X, hbends.trans Sym2.eq_swap⟩
    exact hclosed0 hbBoundary hybetaX hbcolor hybetaMissing
  have hwu1 : w = R.u1 := by
    rw [hTgammaVertices] at hwTgamma
    rcases Finset.mem_insert.mp hwTgamma with hwu | hwS
    · exact False.elim (hwu2 hwu)
    · rw [hSgammaVertices] at hwS
      rcases Finset.mem_union.mp hwS with hwOld | hwu
      · exact False.elim (hwNotX (Finset.mem_sdiff.mp hwOld).1)
      · simpa using hwu
  have hbends' : G.ends b = s(u2, R.u1) := by simpa [hwu1] using hbends
  have hbcolorJ2 : psi2 b = some beta := (hpsi2Beta b).mpr hbcolor
  have hu1u0 : R.u1 ≠ D.u0 d := by
    exact @helper_hu1u0_688 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D d R
  have hu1NotSgammaJ : R.u1 ∉ TreeSequenceVertexSet SgammaJ := by
    rw [hSgammaJVertices]
    intro hu
    rcases Finset.mem_union.mp hu with huOld | hu0
    · exact R.u1_outside (Finset.mem_sdiff.mp huOld).1
    · exact hu1u0 (by simpa using hu0)
  have hu1NotTgammaJ : R.u1 ∉ TreeSequenceVertexSet TgammaJ := by
    rw [hTgammaJVertices]
    have hu1u2 : R.u1 ≠ u2 := hu2u1.symm
    simp [hu1u2, hu1NotSgammaJ]
  have hbBoundaryJ : b ∈ BoundaryEdges G
      (TreeSequenceVertexSet TgammaJ) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u2, hu2TgammaJ, R.u1, hu1NotTgammaJ, hbends'⟩
  obtain ⟨U, hAdjoinBeta⟩ :=
    TreeSequenceBoundaryEdgeAppendExists TgammaJ b hbBoundaryJ
  have hUTash : TashkinovTree G e0 psi2 U :=
    tashkinov_adjoin psi2 TgammaJ U b hAdjoinBeta hTgammaJTash beta
      hbcolorJ2 ybeta hybetaTgammaJ hybetaMissingJ2
  have hUVertices : TreeSequenceVertexSet U =
      insert R.u1 (TreeSequenceVertexSet TgammaJ) :=
    adjoin_vertex_set TgammaJ U b u2 R.u1 hbends' hu2TgammaJ
      hu1NotTgammaJ hAdjoinBeta
  have hmax := ScheideGlobalMaximumFixedPairMaximal
    G k e0 psi2 TgammaJ hglobalJ2
  have hforward : TreeSequenceVertexSet TgammaJ ⊆
      TreeSequenceVertexSet U := by
    rw [hUVertices]
    exact Finset.subset_insert _ _
  have hback := hmax.2 U hUTash hforward
  have hu1U : R.u1 ∈ TreeSequenceVertexSet U := by
    rw [hUVertices]
    simp
  exact hu1NotTgammaJ (hback hu1U)

private theorem helper_continuation_563.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let gamma : Fin k := C.gamma i;
    let gammaJ : Fin k := C.gamma j;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let phi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let psi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    let _ : Finset V :=
      {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let _ : Finset V :=
      {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    ∀ (Sgamma SgammaJ : TreeSequence G e0),
    TreeSequenceVertexSet Sgamma =
        TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
              C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪
          { R.u1 } →
    TreeSequenceVertexSet SgammaJ =
        TreeSequenceVertexSet T \
            {C.blockVertex R.blockIndex (0 : Fin (2 : ℕ)),
              C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))} ∪
          {D.u0 d} →
    ∀ u2 ∉ TreeSequenceVertexSet T,
    u2 ≠ R.u1 →
    (∀ (a : Fin C.p) (r : Fin C.s) (b : Fin (2 : ℕ)), C.y a ≠ C.blockVertex r b) →
    (∀ (rho : PartialEdgeColoring E k) (S U : TreeSequence G e0) (f : E),
        TreeSequenceAdjoinEdge S f U →
          TashkinovTree G e0 rho S →
            ∀ (c : Fin k),
              rho f = some c →
                ∀ v ∈ TreeSequenceVertexSet S,
                  c ∈ MissingColors G rho v → TashkinovTree G e0 rho U) →
    (∀ (A B : TreeSequence G e0) (f : E) (x y : V),
        G.ends f = s(x, y) →
          x ∈ TreeSequenceVertexSet A →
            y ∉ TreeSequenceVertexSet A →
              TreeSequenceAdjoinEdge A f B →
                TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A)) →
    ∀ (Tgamma TgammaJ : TreeSequence G e0),
    TashkinovTree G e0 psi2 TgammaJ →
    TreeSequenceVertexSet Tgamma = insert u2 (TreeSequenceVertexSet Sgamma) →
    TreeSequenceVertexSet TgammaJ = insert u2 (TreeSequenceVertexSet SgammaJ) →
    GlobalMaximumTriple G k e0 psi2 TgammaJ →
    ColoredVertexSetClosed G phi X →
    ColoredVertexSetElementary G phi2 (TreeSequenceVertexSet Tgamma) →
    ColoredVertexSetClosed G phi2 (TreeSequenceVertexSet Tgamma) →
    let b0 : Fin C.p := (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let b1 : Fin C.p := (⟨(1 : ℕ), C.p_ge_two⟩ : Fin C.p);
    let y0 : V := C.y b0;
    let y1 : V := C.y b1;
    y0 ∈ X →
    y1 ∈ X →
    let M0 : Finset (Fin k) := MissingColors G phi y0;
    let M1 : Finset (Fin k) := MissingColors G phi y1;
    ∀ beta ∈ M0 ∪ M1,
    beta ≠ D.alpha0 →
    beta ≠ gamma →
    beta ≠ gammaJ →
    D.alpha0 ≠ gamma →
    gamma ≠ gammaJ →
    gamma ≠ (↑d : Fin k) →
    gammaJ ≠ (↑d : Fin k) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ phi1 phi2 psi1 psi2 Ui Uj Sgamma
      SgammaJ hSgammaVertices hSgammaJVertices u2 hu2X hu2u1 base_ne_block tashkinov_adjoin
      adjoin_vertex_set Tgamma TgammaJ hTgammaJTash hTgammaVertices hTgammaJVertices hglobalJ2
      hclosed0 helementary2 hclosed2 b0 b1 y0 y1 hy0X hy1X M0 M1 beta hbetaUnion hbetaAlpha
      hbetaGamma hbetaGammaJ halphaGamma hgammaGammaJ hgammaDelta hgammaJDelta
  let ybeta := if beta ∈ M0 then y0 else y1
  have hybetaMissing : beta ∈ MissingColors G phi ybeta := by
    by_cases hb0 : beta ∈ M0
    · simp [ybeta, hb0, M0]
    · have hb1 : beta ∈ M1 := (Finset.mem_union.mp hbetaUnion).resolve_left hb0
      simpa [ybeta, hb0, M1] using hb1
  have hybetaCases : ybeta = y0 ∨ ybeta = y1 := by
    by_cases hb0 : beta ∈ M0
    · exact Or.inl (by simp [ybeta, hb0])
    · exact Or.inr (by simp [ybeta, hb0])
  have hybetaX : ybeta ∈ X := by
    rcases hybetaCases with h | h
    · simpa [h] using hy0X
    · simpa [h] using hy1X
  have hbetaDelta : beta ≠ d.1 := by
    exact @helper_hbetaDelta_528 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D d R Sgamma SgammaJ Tgamma TgammaJ hclosed0 beta hybetaMissing hybetaX
  have halphaBeta : D.alpha0 ≠ beta := hbetaAlpha.symm
  have hgammaBeta : gamma ≠ beta := hbetaGamma.symm
  have hgammaJBeta : gammaJ ≠ beta := hbetaGammaJ.symm
  have hdeltaBeta : d.1 ≠ beta := hbetaDelta.symm
  have hphi1Beta : ∀ e : E, phi1 e = some beta ↔ phi e = some beta := by
    intro e
    by_cases hinc : TreeIncidentEdge T e
    · simp [phi1, OutsideTreeColorSwap, hinc]
    · by_cases hea : phi e = some D.alpha0
      · rw [hea]
        simp [phi1, OutsideTreeColorSwap, hinc, hea, halphaBeta, hgammaBeta]
      · by_cases heg : phi e = some gamma
        · rw [heg]
          simp [phi1, OutsideTreeColorSwap, hinc, heg, halphaGamma.symm, halphaBeta, hgammaBeta]
        · simp [phi1, OutsideTreeColorSwap, hinc, hea, heg]
  have hphi2Beta : ∀ e : E, phi2 e = some beta ↔ phi e = some beta := by
    exact @helper_hphi2Beta_559 V E inferInstance inferInstance inferInstance G k e0 phi T C D d
        beta hgammaDelta hgammaBeta hdeltaBeta hphi1Beta
  have hpsi1Beta : ∀ e : E, psi1 e = some beta ↔ phi e = some beta := by
    intro e
    by_cases hinc : TreeIncidentEdge T e
    · simp [psi1, OutsideTreeColorSwap, hinc]
    · by_cases heg : phi e = some gamma
      · rw [heg]
        simp [psi1, OutsideTreeColorSwap, hinc, heg, hgammaBeta, hgammaJBeta]
      · by_cases hegJ : phi e = some gammaJ
        · rw [hegJ]
          simp [psi1, OutsideTreeColorSwap, hinc, hegJ, hgammaGammaJ.symm, hgammaBeta, hgammaJBeta]
        · simp [psi1, OutsideTreeColorSwap, hinc, heg, hegJ]
  have hpsi2Beta : ∀ e : E, psi2 e = some beta ↔ phi e = some beta := by
    exact @helper_hpsi2Beta_583 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 phi T C D d R beta hgammaJDelta hgammaJBeta hdeltaBeta hpsi1Beta
  have missing_iff_of_beta_edges
      (rho sigma : PartialEdgeColoring E k)
      (hedges : ∀ e : E, rho e = some beta ↔ sigma e = some beta)
      (v : V) :
      beta ∈ MissingColors G rho v ↔ beta ∈ MissingColors G sigma v := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro h ⟨e, hve, he⟩
      exact h ⟨e, hve, (hedges e).mpr he⟩
    · intro h ⟨e, hve, he⟩
      exact h ⟨e, hve, (hedges e).mp he⟩
  have hybetaMissing2 : beta ∈ MissingColors G phi2 ybeta :=
    (missing_iff_of_beta_edges phi2 phi hphi2Beta ybeta).mpr hybetaMissing
  have hybetaMissingJ2 : beta ∈ MissingColors G psi2 ybeta :=
    (missing_iff_of_beta_edges psi2 phi hpsi2Beta ybeta).mpr hybetaMissing
  have hybetaNotUi : ybeta ∉ Ui := by
    rcases hybetaCases with h | h
    · rw [h]
      simp [Ui, y0, base_ne_block b0 i 0, base_ne_block b0 i 1]
    · rw [h]
      simp [Ui, y1, base_ne_block b1 i 0, base_ne_block b1 i 1]
  have hybetaNotUj : ybeta ∉ Uj := by
    rcases hybetaCases with h | h
    · rw [h]
      simp [Uj, y0, base_ne_block b0 j 0, base_ne_block b0 j 1]
    · rw [h]
      simp [Uj, y1, base_ne_block b1 j 0, base_ne_block b1 j 1]
  have hybetaSgamma : ybeta ∈ TreeSequenceVertexSet Sgamma := by
    rw [hSgammaVertices]
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mpr ⟨hybetaX, hybetaNotUi⟩))
  have hybetaSgammaJ : ybeta ∈ TreeSequenceVertexSet SgammaJ := by
    rw [hSgammaJVertices]
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mpr ⟨hybetaX, hybetaNotUj⟩))
  have hybetaTgamma : ybeta ∈ TreeSequenceVertexSet Tgamma := by
    rw [hTgammaVertices]
    exact Finset.mem_insert_of_mem hybetaSgamma
  have hybetaTgammaJ : ybeta ∈ TreeSequenceVertexSet TgammaJ := by
    rw [hTgammaJVertices]
    exact Finset.mem_insert_of_mem hybetaSgammaJ
  have hu2Tgamma : u2 ∈ TreeSequenceVertexSet Tgamma := by
    rw [hTgammaVertices]
    simp
  have hu2TgammaJ : u2 ∈ TreeSequenceVertexSet TgammaJ := by
    rw [hTgammaJVertices]
    simp
  have hybetaU2 : ybeta ≠ u2 := by
    intro h
    exact hu2X (h ▸ hybetaX)
  have hbetaNotMissingU2 : beta ∉ MissingColors G phi2 u2 := by
    intro hmissing
    have hdisjoint := helementary2 hybetaTgamma hu2Tgamma hybetaU2
    exact (Finset.disjoint_left.mp hdisjoint) hybetaMissing2 hmissing
  exact @helper_continuation_559 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R Sgamma SgammaJ hSgammaVertices hSgammaJVertices u2 hu2X hu2u1
      tashkinov_adjoin adjoin_vertex_set Tgamma TgammaJ hTgammaJTash hTgammaVertices
      hTgammaJVertices hglobalJ2 hclosed0 hclosed2 beta hybetaMissing hybetaX hphi2Beta hpsi2Beta
      hybetaMissing2 hybetaMissingJ2 hybetaTgamma hybetaTgammaJ hu2Tgamma hu2TgammaJ
      hbetaNotMissingU2
private theorem helper_continuation_588.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T)
      (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T)))
      (R : ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let gamma : Fin k := C.gamma i;
    let gammaJ : Fin k := C.gamma j;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let phi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let psi2 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    let Ui : Finset V :=
      {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V :=
      {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    IsProperEdgeColoring G
        (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) →
    IsOneEdgeUncolored (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) e0 →
    IsProperEdgeColoring G
        (TwoColorComponentSwap G
          (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex))
          (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) →
    IsOneEdgeUncolored
        (TwoColorComponentSwap G
          (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex))
          (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1))
        e0 →
    ∀ (Sgamma SgammaJ : TreeSequence G e0),
    TreeSequenceVertexSet Sgamma =
        TreeSequenceVertexSet T \
            {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
              C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪
          { R.u1 } →
    TreeSequenceVertexSet SgammaJ =
        TreeSequenceVertexSet T \
            {C.blockVertex R.blockIndex (0 : Fin (2 : ℕ)),
              C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))} ∪
          {D.u0 d} →
    ∀ u2 ∉ TreeSequenceVertexSet T,
    u2 ≠ R.u1 →
    T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s →
    (∀ (a : Fin C.p) (r : Fin C.s) (b : Fin (2 : ℕ)), C.y a ≠ C.blockVertex r b) →
    Ui ⊆ X →
    Uj ⊆ X →
    Ui.card = (2 : ℕ) →
    Uj.card = (2 : ℕ) →
    (∀ (rho : PartialEdgeColoring E k) (S U : TreeSequence G e0) (f : E),
        TreeSequenceAdjoinEdge S f U →
          TashkinovTree G e0 rho S →
            ∀ (c : Fin k),
              rho f = some c →
                ∀ v ∈ TreeSequenceVertexSet S,
                  c ∈ MissingColors G rho v → TashkinovTree G e0 rho U) →
    (∀ (A B : TreeSequence G e0) (f : E) (x y : V),
        G.ends f = s(x, y) →
          x ∈ TreeSequenceVertexSet A →
            y ∉ TreeSequenceVertexSet A →
              TreeSequenceAdjoinEdge A f B →
                TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A)) →
    u2 ∉ TreeSequenceVertexSet Sgamma →
    u2 ∉ TreeSequenceVertexSet SgammaJ →
    ∀ (Tgamma TgammaJ : TreeSequence G e0),
    TashkinovTree G e0 phi2 Tgamma →
    TashkinovTree G e0 psi2 TgammaJ →
    TreeSequenceVertexSet Tgamma = insert u2 (TreeSequenceVertexSet Sgamma) →
    TreeSequenceVertexSet TgammaJ = insert u2 (TreeSequenceVertexSet SgammaJ) →
    (TreeSequenceVertexSet Sgamma).card = X.card - (1 : ℕ) →
    (TreeSequenceVertexSet SgammaJ).card = X.card - (1 : ℕ) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ phi1 phi2 psi1 psi2 Ui Uj hproper1
      hone1 hproperJ2 honeJ2 Sgamma SgammaJ hSgammaVertices hSgammaJVertices u2 hu2X hu2u1
      hlength base_ne_block hUiSub hUjSub hUiCard hUjCard tashkinov_adjoin adjoin_vertex_set
      hu2NotSgamma hu2NotSgammaJ Tgamma TgammaJ hTgammaTash hTgammaJTash hTgammaVertices
      hTgammaJVertices hSgammaCard hSgammaJCard
  have hTgammaCard : (TreeSequenceVertexSet Tgamma).card = X.card := by
    rw [hTgammaVertices, Finset.card_insert_of_notMem hu2NotSgamma,
      hSgammaCard]
    have htwo : 2 ≤ X.card := hUiCard ▸ Finset.card_le_card hUiSub
    omega
  have hTgammaJCard : (TreeSequenceVertexSet TgammaJ).card = X.card := by
    rw [hTgammaJVertices, Finset.card_insert_of_notMem hu2NotSgammaJ,
      hSgammaJCard]
    have htwo : 2 ≤ X.card := hUjCard ▸ Finset.card_le_card hUjSub
    omega
  have hproper2 : IsProperEdgeColoring G phi2 := by
    simpa [phi2] using TwoColorComponentSwapProper G phi1 gamma d.1
      (by simpa [gamma, i] using R.gamma_ne_delta) hproper1
        (Sum.inl (D.v0 d))
  have hone2 : IsOneEdgeUncolored phi2 e0 := by
    exact @helper_hone2_388 V E inferInstance inferInstance inferInstance G k e0 phi T C D d hone1
  have hK2 : KTriple G k e0 phi2 :=
    ⟨C.globally_maximum.1.1, C.globally_maximum.1.2.1,
      C.globally_maximum.1.2.2.1, hproper2, hone2⟩
  have hKJ2 : KTriple G k e0 psi2 :=
    ⟨C.globally_maximum.1.1, C.globally_maximum.1.2.1,
      C.globally_maximum.1.2.2.1, hproperJ2, honeJ2⟩
  have horder0 := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hglobal2 : GlobalMaximumTriple G k e0 phi2 Tgamma :=
    ⟨hK2, hTgammaTash, hTgammaCard.trans horder0.1.symm⟩
  have hglobalJ2 : GlobalMaximumTriple G k e0 psi2 TgammaJ :=
    ⟨hKJ2, hTgammaJTash, hTgammaJCard.trans horder0.1.symm⟩
  have hnewOrder := ScheideGlobalMaximumOrder G k e0 phi2 Tgamma hglobal2
  have hnewOrderJ := ScheideGlobalMaximumOrder G k e0 psi2 TgammaJ hglobalJ2
  have helementary0 : ColoredVertexSetElementary G phi X := by
    exact horder0.2.2.2.1
  have hclosed0 : ColoredVertexSetClosed G phi X := by
    exact horder0.2.2.2.2
  have helementary2 : ColoredVertexSetElementary G phi2
      (TreeSequenceVertexSet Tgamma) := hnewOrder.2.2.2.1
  have hclosed2 : ColoredVertexSetClosed G phi2
      (TreeSequenceVertexSet Tgamma) := hnewOrder.2.2.2.2
  let b0 : Fin C.p :=
    ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  let b1 : Fin C.p := ⟨1, C.p_ge_two⟩
  let y0 := C.y b0
  let y1 := C.y b1
  have hy0X : y0 ∈ X := by
    rw [show y0 = T.vertex ⟨0, by omega⟩ by
      simpa [y0, b0] using (C.base_vertex_position b0).symm]
    simp [X, TreeSequenceVertexSet]
  have hy1X : y1 ∈ X := by
    rw [show y1 = T.vertex ⟨1, by
      have hp := C.p_ge_two
      omega⟩ by simpa [y1, b1] using (C.base_vertex_position b1).symm]
    simp [X, TreeSequenceVertexSet]
  have hy01 : y0 ≠ y1 := by
    exact @helper_hy01_441 V E inferInstance inferInstance inferInstance inferInstance G k e0 phi
        T C D d R Sgamma SgammaJ hlength Tgamma TgammaJ
  have he0ends : G.ends e0 = s(y1, y0) := by
    exact @helper_he0ends_454 V E inferInstance inferInstance inferInstance inferInstance G k e0
        phi T C D d R Sgamma SgammaJ hlength Tgamma TgammaJ
  have hy0Incident : Incident G y0 e0 := by simp [Incident, he0ends]
  have hy1Incident : Incident G y1 e0 := by simp [Incident, he0ends]
  have hcount0 :=
    (ScheideGlobalMaximumMissingCounts G k e0 phi T C.globally_maximum
      y0 (by simpa [X] using hy0X)).1 hy0Incident
  have hcount1 :=
    (ScheideGlobalMaximumMissingCounts G k e0 phi T C.globally_maximum
      y1 (by simpa [X] using hy1X)).1 hy1Incident
  let M0 := MissingColors G phi y0
  let M1 := MissingColors G phi y1
  have hMdisjoint : Disjoint M0 M1 := by
    exact helementary0 hy0X hy1X hy01
  have hMcard : 4 ≤ (M0 ∪ M1).card := by
    rw [Finset.card_union_of_disjoint hMdisjoint]
    have hc0 : 2 ≤ M0.card := by simpa [M0] using hcount0.2
    have hc1 : 2 ≤ M1.card := by simpa [M1] using hcount1.2
    omega
  let forbidden : Finset (Fin k) := {D.alpha0, gamma, gammaJ}
  have hforbiddenCard : forbidden.card ≤ 3 := by
    simpa [forbidden] using
      (Finset.card_le_three : ({D.alpha0, gamma, gammaJ} : Finset (Fin k)).card ≤ 3)
  have hnsubset : ¬ M0 ∪ M1 ⊆ forbidden := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨beta, hbetaUnion, hbetaForbidden⟩ :=
    Finset.not_subset.mp hnsubset
  have hbetaForbidden' : beta ≠ D.alpha0 ∧
      beta ≠ gamma ∧ beta ≠ gammaJ := by
    simpa [forbidden] using hbetaForbidden
  have hbetaAlpha : beta ≠ D.alpha0 := by
    exact hbetaForbidden'.1
  have hbetaGamma : beta ≠ gamma := by
    exact hbetaForbidden'.2.1
  have hbetaGammaJ : beta ≠ gammaJ := by
    exact hbetaForbidden'.2.2
  have halphaGamma : D.alpha0 ≠ gamma := by
    simpa [gamma, i] using R.alpha0_ne_gamma
  have hgammaGammaJ : gamma ≠ gammaJ := by
    simpa [gamma, gammaJ, i, j] using R.gamma_ne_gammaJ
  have hgammaDelta : gamma ≠ d.1 := by
    simpa [gamma, i] using R.gamma_ne_delta
  have hgammaJDelta : gammaJ ≠ d.1 := by
    simpa [gammaJ, j] using R.gammaJ_ne_delta
  exact @helper_continuation_563 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R Sgamma SgammaJ hSgammaVertices hSgammaJVertices u2 hu2X hu2u1
      base_ne_block tashkinov_adjoin adjoin_vertex_set Tgamma TgammaJ hTgammaJTash
      hTgammaVertices hTgammaJVertices hglobalJ2 hclosed0 helementary2 hclosed2 hy0X hy1X beta
      hbetaUnion hbetaAlpha hbetaGamma hbetaGammaJ halphaGamma hgammaGammaJ hgammaDelta hgammaJDelta
private theorem helper_continuation_291.{u_1, u_2} :
    helperContinuation291Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ phi1 K phi2 psi1 KJ psi2 Ui Uj
      hproper1 hone1 hstable1 hproperJ2 honeJ2 hdeltaMissingJ2 Sgamma SgammaJ hSgammaTash
      hSgammaVertices hSgammaJTash hSgammaJVertices f2 z2 u2 hf2ends hz2Z hu2X hphi2f2 hpsi2f2
      hu2u0 hu2u1 hlength base_ne_block hUiSub hUjSub hUiCard hUjCard tashkinov_adjoin
  have adjoin_vertex_set (A B : TreeSequence G e0) (f : E) (x y : V)
      (hxy : G.ends f = s(x, y)) (hxA : x ∈ TreeSequenceVertexSet A)
      (hyA : y ∉ TreeSequenceVertexSet A)
      (hAB : TreeSequenceAdjoinEdge A f B) :
      TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A) := by
    exact @helper_adjoin_vertex_set_223 V E inferInstance G e0 A B f x y hxy hyA hAB
  have hz2Sgamma : z2 ∈ TreeSequenceVertexSet Sgamma := by
    rw [hSgammaVertices]
    apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_sdiff.mpr
    exact ⟨(Finset.mem_sdiff.mp hz2Z).1,
      fun hz => (Finset.mem_sdiff.mp hz2Z).2
        (Finset.mem_union.mpr (Or.inl (by simpa [Ui, i] using hz)))⟩
  have hz2SgammaJ : z2 ∈ TreeSequenceVertexSet SgammaJ := by
    rw [hSgammaJVertices]
    apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_sdiff.mpr
    exact ⟨(Finset.mem_sdiff.mp hz2Z).1,
      fun hz => (Finset.mem_sdiff.mp hz2Z).2
        (Finset.mem_union.mpr (Or.inr (by simpa [Uj, j] using hz)))⟩
  have hu2NotSgamma : u2 ∉ TreeSequenceVertexSet Sgamma := by
    rw [hSgammaVertices]
    intro hu
    rcases Finset.mem_union.mp hu with huOld | hu1
    · exact hu2X (Finset.mem_sdiff.mp huOld).1
    · exact hu2u1 (by simpa using hu1)
  have hu2NotSgammaJ : u2 ∉ TreeSequenceVertexSet SgammaJ := by
    rw [hSgammaJVertices]
    intro hu
    rcases Finset.mem_union.mp hu with huOld | hu0
    · exact hu2X (Finset.mem_sdiff.mp huOld).1
    · exact hu2u0 (by simpa using hu0)
  have hf2BoundaryGamma : f2 ∈ BoundaryEdges G
      (TreeSequenceVertexSet Sgamma) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z2, hz2Sgamma, u2, hu2NotSgamma, hf2ends⟩
  have hf2BoundaryGammaJ : f2 ∈ BoundaryEdges G
      (TreeSequenceVertexSet SgammaJ) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z2, hz2SgammaJ, u2, hu2NotSgammaJ, hf2ends⟩
  obtain ⟨Tgamma, hAdjoinGamma⟩ :=
    TreeSequenceBoundaryEdgeAppendExists Sgamma f2 hf2BoundaryGamma
  obtain ⟨TgammaJ, hAdjoinGammaJ⟩ :=
    TreeSequenceBoundaryEdgeAppendExists SgammaJ f2 hf2BoundaryGammaJ
  have hv0X : D.v0 d ∈ X := by
    simpa [X] using (D.replacement_path_full d).1
  have hv0Base : D.v0 d ∈ Finset.univ.image C.y :=
    ScheideStructuralExitsInBase G k e0 phi T C (D.v0_is_exit d)
  obtain ⟨a0, _, ha0⟩ := Finset.mem_image.mp hv0Base
  have hv0NotUi : D.v0 d ∉ Ui := by
    simp [Ui, ← ha0, base_ne_block a0 i 0, base_ne_block a0 i 1]
  have hv0Sgamma : D.v0 d ∈ TreeSequenceVertexSet Sgamma := by
    rw [hSgammaVertices]
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mpr ⟨hv0X, hv0NotUi⟩))
  have hgammaMissing1 : gamma ∈ MissingColors G phi1 (D.v0 d) := by
    rw [hstable1.2 (D.v0 d) (by simpa [X] using hv0X)]
    simpa [gamma, i] using D.gamma_missing_at_v0 d
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi1 gamma d.1
    (by simpa [gamma, i] using R.gamma_ne_delta) hproper1
      (Sum.inl (D.v0 d))
  have hdeltaMissing2 : d.1 ∈ MissingColors G phi2 (D.v0 d) := by
    simpa [phi2, K] using
      hbehavior.2.1 (D.v0 d) (by rfl) hgammaMissing1
  have hTgammaTash : TashkinovTree G e0 phi2 Tgamma :=
    tashkinov_adjoin phi2 Sgamma Tgamma f2 hAdjoinGamma hSgammaTash
      d.1 hphi2f2 (D.v0 d) hv0Sgamma hdeltaMissing2
  have hv1X : R.v1 ∈ X := by simpa [X] using R.v1_mem
  obtain ⟨a1, _, ha1⟩ := Finset.mem_image.mp R.v1_in_base
  have hv1NotUj : R.v1 ∉ Uj := by
    simp [Uj, ← ha1, base_ne_block a1 j 0, base_ne_block a1 j 1]
  have hv1SgammaJ : R.v1 ∈ TreeSequenceVertexSet SgammaJ := by
    rw [hSgammaJVertices]
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mpr ⟨hv1X, hv1NotUj⟩))
  have hTgammaJTash : TashkinovTree G e0 psi2 TgammaJ :=
    tashkinov_adjoin psi2 SgammaJ TgammaJ f2 hAdjoinGammaJ hSgammaJTash
      d.1 hpsi2f2 R.v1 hv1SgammaJ hdeltaMissingJ2
  have hTgammaVertices : TreeSequenceVertexSet Tgamma =
      insert u2 (TreeSequenceVertexSet Sgamma) :=
    adjoin_vertex_set Sgamma Tgamma f2 z2 u2 hf2ends hz2Sgamma
      hu2NotSgamma hAdjoinGamma
  have hTgammaJVertices : TreeSequenceVertexSet TgammaJ =
      insert u2 (TreeSequenceVertexSet SgammaJ) :=
    adjoin_vertex_set SgammaJ TgammaJ f2 z2 u2 hf2ends hz2SgammaJ
      hu2NotSgammaJ hAdjoinGammaJ
  have hSgammaCard : (TreeSequenceVertexSet Sgamma).card = X.card - 1 := by
    rw [hSgammaVertices, Finset.union_singleton,
      Finset.card_insert_of_notMem]
    · rw [Finset.card_sdiff_of_subset hUiSub, hUiCard]
      have htwo : 2 ≤ X.card := hUiCard ▸ Finset.card_le_card hUiSub
      omega
    · exact fun h => R.u1_outside (Finset.mem_sdiff.mp h).1
  have hSgammaJCard : (TreeSequenceVertexSet SgammaJ).card = X.card - 1 := by
    rw [hSgammaJVertices, Finset.union_singleton,
      Finset.card_insert_of_notMem]
    · rw [Finset.card_sdiff_of_subset hUjSub, hUjCard]
      have htwo : 2 ≤ X.card := hUjCard ▸ Finset.card_le_card hUjSub
      omega
    · exact fun h => D.u0_outside d (Finset.mem_sdiff.mp h).1
  exact @helper_continuation_588 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R hproper1 hone1 hproperJ2 honeJ2 Sgamma SgammaJ hSgammaVertices
      hSgammaJVertices u2 hu2X hu2u1 hlength base_ne_block hUiSub hUjSub hUiCard hUjCard
      tashkinov_adjoin adjoin_vertex_set hu2NotSgamma hu2NotSgammaJ Tgamma TgammaJ hTgammaTash
      hTgammaJTash hTgammaVertices hTgammaJVertices hSgammaCard hSgammaJCard
theorem ScheideDefectiveReturnContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)}) :
    ∀ _ : ScheideDefectiveReturnData G k e0 phi T C D d,
    False := by
  classical
  intro R
  let X := TreeSequenceVertexSet T
  let i := D.gammaIndex d
  let j := R.blockIndex
  let gamma := C.gamma i
  let gammaJ := C.gamma j
  let phi1 := OutsideTreeColorSwap T phi D.alpha0 gamma
  let K := TwoColorComponent G phi1 gamma d.1 (Sum.inl (D.v0 d))
  let phi2 := TwoColorComponentSwap G phi1 gamma d.1 (Sum.inl (D.v0 d))
  let psi1 := OutsideTreeColorSwap T phi gamma gammaJ
  let KJ := TwoColorComponent G psi1 gammaJ d.1 (Sum.inl R.v1)
  let psi2 := TwoColorComponentSwap G psi1 gammaJ d.1 (Sum.inl R.v1)
  let Ui := ({C.blockVertex i 0, C.blockVertex i 1} : Finset V)
  let Uj := ({C.blockVertex j 0, C.blockVertex j 1} : Finset V)
  have hterminal := ScheideDefectiveTerminalComponent G k e0 phi T C D d
  dsimp only at hterminal
  rcases hterminal with
    ⟨hproper1, hone1, hstable1, hfixed1, htailK, hf0K, hKtree,
      htreeEdgesOutside, hKcolors⟩
  have hterminalJ :=
    ScheideDefectiveSecondTerminalComponent G k e0 phi T C D d R
  dsimp only at hterminalJ
  rcases hterminalJ with
    ⟨hproperJ1, honeJ1, hstableJ1, hfixedJ1, htailKJ, hf1KJ, hKJtree,
      htreeEdgesOutsideJ, hf1colorJ1, hproperJ2, honeJ2, hdeltaMissingJ2,
      hotherMissingJ2, hf0colorJ2⟩
  have hpairs := ScheideDefectiveDeletedTreePair G k e0 phi T C D d R
  dsimp only at hpairs
  rcases hpairs with
    ⟨Sgamma, SgammaJ, hSgammaTash, hSgammaVertices,
      hSgammaJTash, hSgammaJVertices, hf1color2, hf0colorJ2'⟩
  have hthird := ScheideDefectiveThirdBoundaryEdge G k e0 phi T C D d R
  dsimp only at hthird
  rcases hthird with
    ⟨f2, z2, u2, hf2color, hf2ends, hz2Z, hu2X, hf2f0, hf2f1,
      hz2v0, hz2v1, hphi2f2, hpsi2f2, hu2u0, hu2u1⟩
  have hlength := C.length_eq
  have block_pair_ne (r : Fin C.s) :
      C.blockVertex r 0 ≠ C.blockVertex r 1 := by
    intro h
    let q0 : Fin (T.length + 1) := ⟨C.p + 2 * r.val, by
      have hr := r.isLt
      omega⟩
    let q1 : Fin (T.length + 1) := ⟨C.p + 2 * r.val + 1, by
      have hr := r.isLt
      omega⟩
    have hv : T.vertex q0 = T.vertex q1 := by
      rw [show T.vertex q0 = C.blockVertex r 0 by
        simpa [q0] using C.block_vertex_position r 0]
      rw [show T.vertex q1 = C.blockVertex r 1 by
        simpa [q1] using C.block_vertex_position r 1]
      exact h
    have hq := congrArg Fin.val (T.vertex_injective hv)
    dsimp [q0, q1] at hq
    omega
  have block_mem_X (r : Fin C.s) (b : Fin 2) :
      C.blockVertex r b ∈ X := by
    rw [← C.block_vertex_position r b]
    simp [X, TreeSequenceVertexSet]
  have base_ne_block (a : Fin C.p) (r : Fin C.s) (b : Fin 2) :
      C.y a ≠ C.blockVertex r b := by
    intro h
    let qa : Fin (T.length + 1) := ⟨a.val, by
      have ha := a.isLt
      omega⟩
    let qb : Fin (T.length + 1) :=
      ⟨C.p + 2 * r.val + b.val, by
        have hr := r.isLt
        have hb := b.isLt
        omega⟩
    have hv : T.vertex qa = T.vertex qb := by
      rw [show T.vertex qa = C.y a by
        simpa [qa] using C.base_vertex_position a]
      rw [show T.vertex qb = C.blockVertex r b by
        simpa [qb] using C.block_vertex_position r b]
      exact h
    have hq := congrArg Fin.val (T.vertex_injective hv)
    have ha := a.isLt
    dsimp [qa, qb] at hq
    omega
  have hUiSub : Ui ⊆ X := by
    intro v hv
    simp only [Ui, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact block_mem_X i 0
    · exact block_mem_X i 1
  have hUjSub : Uj ⊆ X := by
    intro v hv
    simp only [Uj, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact block_mem_X j 0
    · exact block_mem_X j 1
  have hUiCard : Ui.card = 2 := by simp [Ui, block_pair_ne i]
  have hUjCard : Uj.card = 2 := by simp [Uj, block_pair_ne j]
  have tashkinov_adjoin (rho : PartialEdgeColoring E k)
      (S U : TreeSequence G e0) (f : E)
      (hadjoin : TreeSequenceAdjoinEdge S f U)
      (hS : TashkinovTree G e0 rho S) (c : Fin k)
      (hf : rho f = some c) (v : V) (hv : v ∈ TreeSequenceVertexSet S)
      (hmiss : c ∈ MissingColors G rho v) :
      TashkinovTree G e0 rho U := by
    exact @helper_tashkinov_adjoin_165 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 phi T C D d R rho S U f hadjoin hS c hf v hv hmiss
  exact @helper_continuation_291 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R hproper1 hone1 hstable1 hproperJ2 honeJ2 hdeltaMissingJ2 Sgamma SgammaJ
      hSgammaTash hSgammaVertices hSgammaJTash hSgammaJVertices f2 z2 u2 hf2ends hz2Z hu2X
      hphi2f2 hpsi2f2 hu2u0 hu2u1 hlength base_ne_block hUiSub hUjSub hUiCard hUjCard
      tashkinov_adjoin
end GoldbergSeymour

end
