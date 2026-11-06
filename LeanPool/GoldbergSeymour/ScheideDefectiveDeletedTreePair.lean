/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.ScheideDefectiveDeletedTreePair

public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.ScheideDefectiveReturnData
public import LeanPool.GoldbergSeymour.ScheideDefectiveSecondTerminalComponent
public import LeanPool.GoldbergSeymour.ScheideDefectiveTerminalComponent
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumUnused
public import LeanPool.GoldbergSeymour.ScheideSelectedBlockDeletion
public import LeanPool.GoldbergSeymour.ScheideStructuralExitsInBase
public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Scheide Defective Deleted Tree Pair

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation619Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let _ : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let gamma : Fin k := C.gamma i;
    let gammaJ : Fin k := C.gamma j;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let psi2 : PartialEdgeColoring E k := TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k)
        (Sum.inl R.v1); StableColoring T ∅ phi (OutsideTreeColorSwap T phi D.alpha0 (C.gamma
        (D.gammaIndex d))) → StableColoring T ∅ phi (OutsideTreeColorSwap T phi (C.gamma
        (D.gammaIndex d)) (C.gamma R.blockIndex)) → (↑d : Fin k) ∈ MissingColors G
        (TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) R.v1 →
        TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1) (D.f0 d) = some (↑d :
        Fin k) → (
    have C_1 : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    have phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k)
        (Sum.inl (D.v0 d)); (
    ∀ (v : V), Sum.inl v ∉ C_1 → MissingColors G phi' v = MissingColors G phi1 v) ∧ (
    ∀ (v : V), Sum.inl v ∈ C_1 → gamma ∈ MissingColors G phi1 v → (↑d : Fin k) ∈ MissingColors G
        phi' v) ∧ (
    ∀ (v : V), Sum.inl v ∈ C_1 → (↑d : Fin k) ∈ MissingColors G phi1 v → gamma ∈ MissingColors G
        phi' v) ∧
    ∀ (v : V) (c : Fin k), c ≠ gamma → c ≠ (↑d : Fin k) → (c ∈ MissingColors G phi' v ↔ c ∈
        MissingColors G phi1 v)) → (
    have C_1 : Set (V ⊕ E) := TwoColorComponent G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    have phi' : PartialEdgeColoring E k := TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k)
        (Sum.inl R.v1); (
    ∀ (v : V), Sum.inl v ∉ C_1 → MissingColors G phi' v = MissingColors G psi1 v) ∧ (
    ∀ (v : V), Sum.inl v ∈ C_1 → gammaJ ∈ MissingColors G psi1 v → (↑d : Fin k) ∈ MissingColors G
        phi' v) ∧ (
    ∀ (v : V), Sum.inl v ∈ C_1 → (↑d : Fin k) ∈ MissingColors G psi1 v → gammaJ ∈ MissingColors G
        phi' v) ∧
    ∀ (v : V) (c : Fin k), c ≠ gammaJ → c ≠ (↑d : Fin k) → (c ∈ MissingColors G phi' v ↔ c ∈
        MissingColors G psi1 v)) → (↑d : Fin k) ∈ MissingColors G phi2 (D.v0 d) → phi2 R.f1 = some
        (↑d : Fin k) →
    ∀ (Tgamma : TreeSequence G e0), TreeSequenceVertexSet Tgamma = TreeSequenceVertexSet T \
        {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))} → Tgamma.length +
        (2 : ℕ) = T.length → (
    ∀ (a : Fin C.p),
    ∃ (q : Fin (Tgamma.length + (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ Tgamma.vertex q = C.y a) → (
    ∀ (q : Fin Tgamma.length), (
    ∃ (a : Fin (C.p - (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ Tgamma.edge q = C.baseEdge a) ∨
    ∃ (r : Fin C.s) (j : Fin (2 : ℕ)), r ≠ i ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ Tgamma.edge q =
        C.blockEdge r j) →
    ∀ (TgammaJ : TreeSequence G e0), TreeSequenceVertexSet TgammaJ = TreeSequenceVertexSet T \
        {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))} → TgammaJ.length +
        (2 : ℕ) = T.length → (
    ∀ (a : Fin C.p),
    ∃ (q : Fin (TgammaJ.length + (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ TgammaJ.vertex q = C.y a) → (
    ∀ (q : Fin TgammaJ.length), (
    ∃ (a : Fin (C.p - (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ TgammaJ.edge q = C.baseEdge a) ∨
    ∃ (r : Fin C.s) (j_1 : Fin (2 : ℕ)), r ≠ j ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ TgammaJ.edge q =
        C.blockEdge r j_1) → TashkinovTree G e0 phi T → Disjoint (DefectiveColors G phi
        (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧ Disjoint (TreeFreeColors phi T)
        (TreeUsedColors phi T) → (
    ∀ (q : Fin T.length) (c : Fin k), phi (T.edge q) = some c → phi2 (T.edge q) = some c) → (
    ∀ (q : Fin T.length) (c : Fin k), phi (T.edge q) = some c → psi2 (T.edge q) = some c) →
    ∃ (Sgamma : TreeSequence G e0) (SgammaJ : TreeSequence G e0), TashkinovTree G e0
        (TwoColorComponentSwap G (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)))
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) Sgamma ∧ TreeSequenceVertexSet
        Sgamma = TreeSequenceVertexSet T \ {C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪ { R.u1 } ∧ TashkinovTree G e0
        (TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) SgammaJ ∧
        TreeSequenceVertexSet SgammaJ = TreeSequenceVertexSet T \ {C.blockVertex R.blockIndex (0 :
        Fin (2 : ℕ)), C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))} ∪ {D.u0 d} ∧
        TwoColorComponentSwap G (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)))
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) R.f1 = some (↑d : Fin k) ∧
        TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1) (D.f0 d) = some (↑d :
        Fin k)

private theorem helper_htreeGamma_196.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    ∀ (Tgamma : TreeSequence G e0), Tgamma.length + (2 : ℕ) = T.length → (
    ∀ (a : Fin C.p),
    ∃ (q : Fin (Tgamma.length + (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ Tgamma.vertex q = C.y a) → (
    ∀ (q : Fin Tgamma.length), (
    ∃ (a : Fin (C.p - (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ Tgamma.edge q = C.baseEdge a) ∨
    ∃ (r : Fin C.s) (j : Fin (2 : ℕ)), r ≠ i ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ Tgamma.edge q =
        C.blockEdge r j) →
    ∀ (TgammaJ : TreeSequence G e0), TgammaJ.length + (2 : ℕ) = T.length → TashkinovTree G e0 phi
        T → Disjoint (DefectiveColors G phi (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧
        Disjoint (TreeFreeColors phi T) (TreeUsedColors phi T) → (
    ∀ (q : Fin T.length) (c : Fin k), phi (T.edge q) = some c → phi2 (T.edge q) = some c) → (
    ∀ v ∈ X,
    ∀ (c : Fin k), c ≠ gamma → c ≠ (↑d : Fin k) → (c ∈ MissingColors G phi2 v ↔ c ∈ MissingColors
        G phi v)) → TashkinovTree G e0 phi2 Tgamma := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X i gamma phi1 phi2 Tgamma hTgammaLength hTgammaBaseVertices
      hTgammaEdgeCases TgammaJ hTgammaJLength htreeOld hunused edge_color_phi2 missing_unaffected
      q hq
  rcases hTgammaEdgeCases q with
    ⟨a, hqa, hqe⟩ | ⟨r, b, hri, hqbase, hqe⟩
  · have haPos : 1 ≤ a.val := by omega
    let oldq : Fin T.length := ⟨a.val, by omega⟩
    obtain ⟨w, c, hc, hm⟩ := htreeOld oldq haPos
    have hwP : w.val < C.p := by
      have hw := w.isLt
      dsimp [oldq] at hw
      omega
    let wp : Fin C.p := ⟨w.val, hwP⟩
    obtain ⟨ws, hwsval, hws⟩ := hTgammaBaseVertices wp
    have hwq : w.val < q.val + 1 := by
      have hw := w.isLt
      dsimp [oldq] at hw
      omega
    let wn : Fin (q.val + 1) := ⟨w.val, hwq⟩
    have hcast : Fin.castLT wn
        (Nat.lt_trans wn.isLt (Nat.succ_lt_succ q.isLt)) = ws := by
      apply Fin.ext
      simpa [wn] using hwsval.symm
    have holdedge : T.edge oldq = C.baseEdge a := by
      simpa [oldq] using C.base_edge_position a
    have hcbase : phi (C.baseEdge a) = some c := holdedge ▸ hc
    have hcGamma : c ≠ gamma := by
      simpa [gamma, i] using
        C.initial_nonfirst_avoids_blocks a haPos c hcbase i
    have hcUsed : c ∈ TreeUsedColors phi T := by
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨oldq, haPos, hc⟩
    have hcDelta : c ≠ d.1 := by
      intro heq
      exact (Finset.disjoint_left.mp hunused.1) d.2 (heq ▸ hcUsed)
    refine ⟨wn, c, ?_, ?_⟩
    · rw [hqe, ← holdedge]
      exact edge_color_phi2 oldq c hc
    · rw [hcast, hws]
      have hvwpX : C.y wp ∈ X := by
        rw [← C.base_vertex_position wp]
        simp [X, TreeSequenceVertexSet]
      have holdvertex : T.vertex
          (Fin.castLT w (Nat.lt_trans w.isLt (Nat.succ_lt_succ oldq.isLt))) =
          C.y wp := by
        have hidx : Fin.castLT w
            (Nat.lt_trans w.isLt (Nat.succ_lt_succ oldq.isLt)) =
            (⟨wp.val, by omega⟩ : Fin (T.length + 1)) := by
          apply Fin.ext
          rfl
        rw [hidx]
        exact C.base_vertex_position wp
      have hmwp : c ∈ MissingColors G phi (C.y wp) := by
        simpa only [holdvertex] using hm
      exact (missing_unaffected (C.y wp) hvwpX c hcGamma hcDelta).mpr hmwp
  · obtain ⟨w, hwmissing⟩ := C.block_color_missing_on_base r
    obtain ⟨ws, hwsval, hws⟩ := hTgammaBaseVertices w
    let wn : Fin (q.val + 1) := ⟨w.val, by omega⟩
    have hcast : Fin.castLT wn
        (Nat.lt_trans wn.isLt (Nat.succ_lt_succ q.isLt)) = ws := by
      apply Fin.ext
      simpa [wn] using hwsval.symm
    have hrgamma : C.gamma r ≠ gamma := by
      intro h
      exact hri (C.gamma_injective (by simpa [gamma, i] using h))
    let oldq : Fin T.length := ⟨C.p - 1 + 2 * r.val + b.val, by
      have hr := r.isLt
      have hb := b.isLt
      have hlen := C.length_eq
      omega⟩
    have hrdelta : C.gamma r ≠ d.1 := by
      intro h
      have hused : d.1 ∈ TreeUsedColors phi T := by
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨oldq, by
          have hp := C.p_ge_two
          simp [oldq]
          omega, ?_⟩
        rw [show T.edge oldq = C.blockEdge r b by
          simpa [oldq] using C.block_edge_position r b]
        simpa [h] using C.block_color r b
      exact (Finset.disjoint_left.mp hunused.1) d.2 hused
    have holdedge : T.edge oldq = C.blockEdge r b := by
      simpa only [oldq] using C.block_edge_position r b
    have hcold : phi (T.edge oldq) = some (C.gamma r) := by
      rw [holdedge]
      exact C.block_color r b
    refine ⟨wn, C.gamma r, ?_, ?_⟩
    · rw [hqe, ← holdedge]
      exact edge_color_phi2 oldq (C.gamma r) hcold
    · rw [hcast, hws]
      exact (missing_unaffected (C.y w) (by
        rw [← C.base_vertex_position w]
        simp [X, TreeSequenceVertexSet])
        (C.gamma r) hrgamma hrdelta).mpr hwmissing

private theorem helper_htreeGammaJ_291.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let gamma : Fin k := C.gamma i;
    let gammaJ : Fin k := C.gamma j;
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let psi2 : PartialEdgeColoring E k := TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k)
        (Sum.inl R.v1);
    ∀ (_ TgammaJ : TreeSequence G e0), TgammaJ.length + (2 : ℕ) = T.length → (
    ∀ (a : Fin C.p),
    ∃ (q : Fin (TgammaJ.length + (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ TgammaJ.vertex q = C.y a) → (
    ∀ (q : Fin TgammaJ.length), (
    ∃ (a : Fin (C.p - (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ TgammaJ.edge q = C.baseEdge a) ∨
    ∃ (r : Fin C.s) (j_1 : Fin (2 : ℕ)), r ≠ j ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ TgammaJ.edge q =
        C.blockEdge r j_1) → TashkinovTree G e0 phi T → Disjoint (DefectiveColors G phi
        (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧ Disjoint (TreeFreeColors phi T)
        (TreeUsedColors phi T) → (
    ∀ (q : Fin T.length) (c : Fin k), phi (T.edge q) = some c → psi2 (T.edge q) = some c) → (
    ∀ v ∈ X,
    ∀ (c : Fin k), c ≠ gammaJ → c ≠ (↑d : Fin k) → (c ∈ MissingColors G psi2 v ↔ c ∈ MissingColors
        G phi v)) → TashkinovTree G e0 psi2 TgammaJ := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ psi1 psi2 Tgamma TgammaJ
      hTgammaJLength hTgammaJBaseVertices hTgammaJEdgeCases htreeOld hunused edge_color_psi2
      missing_unaffectedJ q hq
  rcases hTgammaJEdgeCases q with
    ⟨a, hqa, hqe⟩ | ⟨r, b, hrj, hqbase, hqe⟩
  · have haPos : 1 ≤ a.val := by omega
    let oldq : Fin T.length := ⟨a.val, by omega⟩
    obtain ⟨w, c, hc, hm⟩ := htreeOld oldq haPos
    have hwP : w.val < C.p := by
      have hw := w.isLt
      dsimp [oldq] at hw
      omega
    let wp : Fin C.p := ⟨w.val, hwP⟩
    obtain ⟨ws, hwsval, hws⟩ := hTgammaJBaseVertices wp
    have hwq : w.val < q.val + 1 := by
      have hw := w.isLt
      dsimp [oldq] at hw
      omega
    let wn : Fin (q.val + 1) := ⟨w.val, hwq⟩
    have hcast : Fin.castLT wn
        (Nat.lt_trans wn.isLt (Nat.succ_lt_succ q.isLt)) = ws := by
      apply Fin.ext
      simpa [wn] using hwsval.symm
    have holdedge : T.edge oldq = C.baseEdge a := by
      simpa [oldq] using C.base_edge_position a
    have hcbase : phi (C.baseEdge a) = some c := holdedge ▸ hc
    have hcGammaJ : c ≠ gammaJ := by
      simpa [gammaJ, j] using
        C.initial_nonfirst_avoids_blocks a haPos c hcbase j
    have hcUsed : c ∈ TreeUsedColors phi T := by
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨oldq, haPos, hc⟩
    have hcDelta : c ≠ d.1 := by
      intro heq
      exact (Finset.disjoint_left.mp hunused.1) d.2 (heq ▸ hcUsed)
    refine ⟨wn, c, ?_, ?_⟩
    · rw [hqe, ← holdedge]
      exact edge_color_psi2 oldq c hc
    · rw [hcast, hws]
      have hvwpX : C.y wp ∈ X := by
        rw [← C.base_vertex_position wp]
        simp [X, TreeSequenceVertexSet]
      have holdvertex : T.vertex
          (Fin.castLT w (Nat.lt_trans w.isLt (Nat.succ_lt_succ oldq.isLt))) =
          C.y wp := by
        have hidx : Fin.castLT w
            (Nat.lt_trans w.isLt (Nat.succ_lt_succ oldq.isLt)) =
            (⟨wp.val, by omega⟩ : Fin (T.length + 1)) := by
          apply Fin.ext
          rfl
        rw [hidx]
        exact C.base_vertex_position wp
      have hmwp : c ∈ MissingColors G phi (C.y wp) := by
        simpa only [holdvertex] using hm
      exact (missing_unaffectedJ (C.y wp) hvwpX c hcGammaJ hcDelta).mpr hmwp
  · obtain ⟨w, hwmissing⟩ := C.block_color_missing_on_base r
    obtain ⟨ws, hwsval, hws⟩ := hTgammaJBaseVertices w
    let wn : Fin (q.val + 1) := ⟨w.val, by omega⟩
    have hcast : Fin.castLT wn
        (Nat.lt_trans wn.isLt (Nat.succ_lt_succ q.isLt)) = ws := by
      apply Fin.ext
      simpa [wn] using hwsval.symm
    have hrgamma : C.gamma r ≠ gammaJ := by
      intro h
      exact hrj (C.gamma_injective (by simpa [gammaJ, j] using h))
    let oldq : Fin T.length := ⟨C.p - 1 + 2 * r.val + b.val, by
      have hr := r.isLt
      have hb := b.isLt
      have hlen := C.length_eq
      omega⟩
    have hrdelta : C.gamma r ≠ d.1 := by
      intro h
      have hused : d.1 ∈ TreeUsedColors phi T := by
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨oldq, by
          have hp := C.p_ge_two
          simp [oldq]
          omega, ?_⟩
        rw [show T.edge oldq = C.blockEdge r b by
          simpa [oldq] using C.block_edge_position r b]
        simpa [h] using C.block_color r b
      exact (Finset.disjoint_left.mp hunused.1) d.2 hused
    have holdedge : T.edge oldq = C.blockEdge r b := by
      simpa only [oldq] using C.block_edge_position r b
    have hcold : phi (T.edge oldq) = some (C.gamma r) := by
      rw [holdedge]
      exact C.block_color r b
    refine ⟨wn, C.gamma r, ?_, ?_⟩
    · rw [hqe, ← holdedge]
      exact edge_color_psi2 oldq (C.gamma r) hcold
    · rw [hcast, hws]
      exact (missing_unaffectedJ (C.y w) (by
        rw [← C.base_vertex_position w]
        simp [X, TreeSequenceVertexSet])
        (C.gamma r) hrgamma hrdelta).mpr hwmissing

private theorem helper_tashkinov_adjoin_386.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    ∀ (_ _ S U : TreeSequence G e0) (f : E), TreeSequenceAdjoinEdge S f U → TashkinovTree G e0
        phi2 S →
    ∀ (c : Fin k), phi2 f = some c →
    ∀ v ∈ TreeSequenceVertexSet S, c ∈ MissingColors G phi2 v → TashkinovTree G e0 phi2 U := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i gamma phi1 phi2 Tgamma TgammaJ S U f hadjoin hS c hf v hv
      hmiss
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
      simpa [oldVertexIndex, newVertexIndex] using hvertex.symm ▸ hcolorMissing
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

private theorem helper_tashkinov_adjoinJ_443.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let gamma : Fin k := C.gamma i;
    let gammaJ : Fin k := C.gamma j;
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let psi2 : PartialEdgeColoring E k := TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k)
        (Sum.inl R.v1);
    ∀ (_ _ S U : TreeSequence G e0) (f : E), TreeSequenceAdjoinEdge S f U → TashkinovTree G e0
        psi2 S →
    ∀ (c : Fin k), psi2 f = some c →
    ∀ v ∈ TreeSequenceVertexSet S, c ∈ MissingColors G psi2 v → TashkinovTree G e0 psi2 U := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R i j gamma gammaJ psi1 psi2 Tgamma TgammaJ S U f hadjoin
      hS c hf v hv hmiss
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
      simpa [oldVertexIndex, newVertexIndex] using hvertex.symm ▸ hcolorMissing
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

private theorem helper_continuation_619.{u_1, u_2} :
    helperContinuation619Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ phi1 phi2 psi1 psi2 hstable1
      hstableJ1 hdeltaMissingJ2 hf0colorJ2 hbehavior hbehaviorJ hdeltaMissing2 hf1color2 Tgamma
      hTgammaVertices hTgammaLength hTgammaBaseVertices hTgammaEdgeCases TgammaJ hTgammaJVertices
      hTgammaJLength hTgammaJBaseVertices hTgammaJEdgeCases htreeOld hunused edge_color_phi2
      edge_color_psi2
  have missing_unaffected (v : V) (hvX' : v ∈ X) (c : Fin k)
      (hcg : c ≠ gamma) (hcd : c ≠ d.1) :
      (c ∈ MissingColors G phi2 v ↔ c ∈ MissingColors G phi v) := by
    have h1 : MissingColors G phi1 v = MissingColors G phi v :=
      hstable1.2 v (by simpa [X] using hvX')
    rw [← h1]
    exact hbehavior.2.2.2 v c hcg hcd
  have missing_unaffectedJ (v : V) (hvX' : v ∈ X) (c : Fin k)
      (hcg : c ≠ gammaJ) (hcd : c ≠ d.1) :
      (c ∈ MissingColors G psi2 v ↔ c ∈ MissingColors G phi v) := by
    have h1 : MissingColors G psi1 v = MissingColors G phi v :=
      hstableJ1.2 v (by simpa [X] using hvX')
    rw [← h1]
    exact hbehaviorJ.2.2.2 v c hcg hcd
  have htreeGamma := @helper_htreeGamma_196 V E inferInstance inferInstance inferInstance G k e0 phi
      T C D d Tgamma hTgammaLength hTgammaBaseVertices hTgammaEdgeCases TgammaJ hTgammaJLength
      htreeOld hunused edge_color_phi2 missing_unaffected
  have htreeGammaJ := @helper_htreeGammaJ_291 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R Tgamma TgammaJ hTgammaJLength hTgammaJBaseVertices
      hTgammaJEdgeCases htreeOld hunused edge_color_psi2 missing_unaffectedJ
  have tashkinov_adjoin := @helper_tashkinov_adjoin_386 V E inferInstance inferInstance
      inferInstance G k e0 phi T C D d Tgamma TgammaJ
  have tashkinov_adjoinJ := @helper_tashkinov_adjoinJ_443 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 phi T C D d R Tgamma TgammaJ
  have adjoin_vertex_set (A B : TreeSequence G e0) (f : E) (x y : V)
      (hxy : G.ends f = s(x, y)) (hxA : x ∈ TreeSequenceVertexSet A)
      (hyA : y ∉ TreeSequenceVertexSet A)
      (hAB : TreeSequenceAdjoinEdge A f B) :
      TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A) := by
    exact @SharedFacts.ScheideDefectiveDeletedTreePair.adjoin_vertex_set V E inferInstance G
        e0 A B f x y hxy hyA hAB
  have hv0Gamma : D.v0 d ∈ TreeSequenceVertexSet Tgamma := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp
      (ScheideStructuralExitsInBase G k e0 phi T C (D.v0_is_exit d))
    obtain ⟨q, hq, hvertex⟩ := hTgammaBaseVertices a
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨q, hvertex.trans ha⟩
  have hv1Gamma : R.v1 ∈ TreeSequenceVertexSet Tgamma := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp R.v1_in_base
    obtain ⟨q, hq, hvertex⟩ := hTgammaBaseVertices a
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨q, hvertex.trans ha⟩
  have hu1NotGamma : R.u1 ∉ TreeSequenceVertexSet Tgamma := by
    rw [hTgammaVertices]
    exact fun h => R.u1_outside (Finset.mem_sdiff.mp h).1
  have hf1Boundary : R.f1 ∈ BoundaryEdges G (TreeSequenceVertexSet Tgamma) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R.v1, hv1Gamma, R.u1, hu1NotGamma, R.f1_ends⟩
  obtain ⟨Sgamma, hAdjoinGamma⟩ :=
    TreeSequenceBoundaryEdgeAppendExists Tgamma R.f1 hf1Boundary
  have hSgammaTash : TashkinovTree G e0 phi2 Sgamma :=
    tashkinov_adjoin Tgamma Sgamma R.f1 hAdjoinGamma htreeGamma d.1
      hf1color2 (D.v0 d) hv0Gamma hdeltaMissing2
  have hSgammaVertices0 : TreeSequenceVertexSet Sgamma =
      insert R.u1 (TreeSequenceVertexSet Tgamma) :=
    adjoin_vertex_set Tgamma Sgamma R.f1 R.v1 R.u1 R.f1_ends
      hv1Gamma hu1NotGamma hAdjoinGamma
  have hSgammaVertices : TreeSequenceVertexSet Sgamma =
      (TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1}) ∪ {R.u1} := by
    rw [hSgammaVertices0, hTgammaVertices]
    simp [i, Finset.union_singleton]
  have hv0GammaJ : D.v0 d ∈ TreeSequenceVertexSet TgammaJ := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp
      (ScheideStructuralExitsInBase G k e0 phi T C (D.v0_is_exit d))
    obtain ⟨q, hq, hvertex⟩ := hTgammaJBaseVertices a
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨q, hvertex.trans ha⟩
  have hv1GammaJ : R.v1 ∈ TreeSequenceVertexSet TgammaJ := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp R.v1_in_base
    obtain ⟨q, hq, hvertex⟩ := hTgammaJBaseVertices a
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨q, hvertex.trans ha⟩
  have hu0NotGammaJ : D.u0 d ∉ TreeSequenceVertexSet TgammaJ := by
    rw [hTgammaJVertices]
    exact fun h => D.u0_outside d (Finset.mem_sdiff.mp h).1
  have hf0Boundary : D.f0 d ∈ BoundaryEdges G
      (TreeSequenceVertexSet TgammaJ) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨D.v0 d, hv0GammaJ, D.u0 d, hu0NotGammaJ, D.f0_ends d⟩
  obtain ⟨SgammaJ, hAdjoinGammaJ⟩ :=
    TreeSequenceBoundaryEdgeAppendExists TgammaJ (D.f0 d) hf0Boundary
  have hSgammaJTash : TashkinovTree G e0 psi2 SgammaJ :=
    tashkinov_adjoinJ TgammaJ SgammaJ (D.f0 d) hAdjoinGammaJ
      htreeGammaJ d.1 hf0colorJ2 R.v1 hv1GammaJ hdeltaMissingJ2
  have hSgammaJVertices0 : TreeSequenceVertexSet SgammaJ =
      insert (D.u0 d) (TreeSequenceVertexSet TgammaJ) :=
    adjoin_vertex_set TgammaJ SgammaJ (D.f0 d) (D.v0 d) (D.u0 d)
      (D.f0_ends d) hv0GammaJ hu0NotGammaJ hAdjoinGammaJ
  have hSgammaJVertices : TreeSequenceVertexSet SgammaJ =
      (TreeSequenceVertexSet T \
        {C.blockVertex R.blockIndex 0,
          C.blockVertex R.blockIndex 1}) ∪ {D.u0 d} := by
    rw [hSgammaJVertices0, hTgammaJVertices]
    simp [j, Finset.union_singleton]
  exact ⟨Sgamma, SgammaJ, hSgammaTash, hSgammaVertices,
    hSgammaJTash, hSgammaJVertices, hf1color2, hf0colorJ2⟩

theorem ScheideDefectiveDeletedTreePair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideDefectiveReturnData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let gammaJ := C.gamma R.blockIndex
    let phi1 := OutsideTreeColorSwap T phi D.alpha0 gamma
    let phi2 := TwoColorComponentSwap G phi1 gamma d.1 (Sum.inl (D.v0 d))
    let psi1 := OutsideTreeColorSwap T phi gamma gammaJ
    let psi2 := TwoColorComponentSwap G psi1 gammaJ d.1 (Sum.inl R.v1)
    ∃ Sgamma SgammaJ : TreeSequence G e0,
      TashkinovTree G e0 phi2 Sgamma ∧
      TreeSequenceVertexSet Sgamma =
        (TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1}) ∪ {R.u1} ∧
      TashkinovTree G e0 psi2 SgammaJ ∧
      TreeSequenceVertexSet SgammaJ =
        (TreeSequenceVertexSet T \
          {C.blockVertex R.blockIndex 0,
            C.blockVertex R.blockIndex 1}) ∪ {D.u0 d} ∧
      phi2 R.f1 = some d.1 ∧ psi2 (D.f0 d) = some d.1 := by
  classical
  dsimp only
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
  have tree_edge_incident : ∀ q : Fin T.length, TreeIncidentEdge T (T.edge q) := by
    intro q
    obtain ⟨a, ha⟩ := T.attaches q
    refine ⟨T.vertex q.succ, ?_, ?_⟩
    · simp [TreeSequenceVertexSet]
    · simp [Incident, ha]
  have component_vertex_of_edge {v : V} {e : E}
      (heK : Sum.inr e ∈ K) (hve : Incident G v e)
      (hecolor : phi1 e = some gamma ∨ phi1 e = some d.1) :
      Sum.inl v ∈ K := by
    let H := TwoColorIncidenceGraph G phi1 gamma d.1
    have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
      simpa [H, TwoColorIncidenceGraph] using ⟨hve, hecolor⟩
    change H.connectedComponentMk (Sum.inr e) =
      H.connectedComponentMk (Sum.inl (D.v0 d)) at heK
    change H.connectedComponentMk (Sum.inl v) =
      H.connectedComponentMk (Sum.inl (D.v0 d))
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heK
  have hv0X : D.v0 d ∈ X := by
    have hv0base := ScheideStructuralExitsInBase G k e0 phi T C (D.v0_is_exit d)
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv0base
    rw [← ha, ← C.base_vertex_position a]
    simp [X, TreeSequenceVertexSet]
  have hv1X : R.v1 ∈ X := by simpa [X] using R.v1_mem
  have hgammaDelta : gamma ≠ d.1 := by simpa [gamma, i] using R.gamma_ne_delta
  have hgammaJDelta : gammaJ ≠ d.1 := by
    simpa [gammaJ, j] using R.gammaJ_ne_delta
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi1 gamma d.1
    hgammaDelta hproper1 (Sum.inl (D.v0 d))
  have hbehaviorJ := TwoColorComponentSwapMissingBehavior G psi1 gammaJ d.1
    hgammaJDelta hproperJ1 (Sum.inl R.v1)
  have hgammaMissing1 : gamma ∈ MissingColors G phi1 (D.v0 d) := by
    rw [hstable1.2 (D.v0 d) (by simpa [X] using hv0X)]
    simpa [gamma, i] using D.gamma_missing_at_v0 d
  have hdeltaMissing2 : d.1 ∈ MissingColors G phi2 (D.v0 d) := by
    simpa [phi2, K] using
      hbehavior.2.1 (D.v0 d) (by rfl) hgammaMissing1
  have hphi1f1 : phi1 R.f1 = some d.1 := by
    apply (hfixed1 R.f1 ?_).trans R.f1_color
    exact ⟨R.v1, by simpa [X] using hv1X,
      by simp [Incident, R.f1_ends]⟩
  have hf1NotK : Sum.inr R.f1 ∉ K := by
    intro hf1K
    have hv1f1 : Incident G R.v1 R.f1 := by
      simp [Incident, R.f1_ends]
    have hv1K := component_vertex_of_edge hf1K hv1f1 (Or.inr hphi1f1)
    exact R.v1_ne_v0 ((hKtree R.v1 (by simpa [X] using hv1X)).mp hv1K)
  have hf1color2 : phi2 R.f1 = some d.1 := by
    simp [phi2, TwoColorComponentSwap, K, hf1NotK, hphi1f1]
  obtain ⟨Tgamma, hTgammaVertices, hTgammaLength, hTgammaVertexReindex,
      hTgammaEdgeReindex, hTgammaBaseVertices, hTgammaBaseEdges,
      hTgammaBlockEntries, hTgammaEdgeCases, hTgammaEdgeOld,
      hTgammaNotIncident⟩ :=
    ScheideSelectedBlockDeletion G k e0 phi T C i
  obtain ⟨TgammaJ, hTgammaJVertices, hTgammaJLength,
      hTgammaJVertexReindex, hTgammaJEdgeReindex, hTgammaJBaseVertices,
      hTgammaJBaseEdges, hTgammaJBlockEntries, hTgammaJEdgeCases,
      hTgammaJEdgeOld, hTgammaJNotIncident⟩ :=
    ScheideSelectedBlockDeletion G k e0 phi T C j
  have htreeOld : TashkinovTree G e0 phi T := C.globally_maximum.2.1
  have hunused := ScheideGlobalMaximumUnused G k e0 phi T C.globally_maximum
  have edge_color_phi2 (q : Fin T.length) (c : Fin k)
      (hc : phi (T.edge q) = some c) : phi2 (T.edge q) = some c := by
    have hc1 : phi1 (T.edge q) = some c :=
      (hfixed1 _ (tree_edge_incident q)).trans hc
    have hout : Sum.inr (T.edge q) ∉ K := by
      simpa [K] using htreeEdgesOutside q
    simp [phi2, TwoColorComponentSwap, K, hout, hc1]
  have edge_color_psi2 (q : Fin T.length) (c : Fin k)
      (hc : phi (T.edge q) = some c) : psi2 (T.edge q) = some c := by
    have hc1 : psi1 (T.edge q) = some c :=
      (hfixedJ1 _ (tree_edge_incident q)).trans hc
    have hout : Sum.inr (T.edge q) ∉ KJ := by
      simpa [KJ] using htreeEdgesOutsideJ q
    simp [psi2, TwoColorComponentSwap, KJ, hout, hc1]
  exact @helper_continuation_619 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R hstable1 hstableJ1 hdeltaMissingJ2 hf0colorJ2 hbehavior hbehaviorJ
      hdeltaMissing2 hf1color2 Tgamma hTgammaVertices hTgammaLength hTgammaBaseVertices
      hTgammaEdgeCases TgammaJ hTgammaJVertices hTgammaJLength hTgammaJBaseVertices
      hTgammaJEdgeCases htreeOld hunused edge_color_phi2 edge_color_psi2
end GoldbergSeymour

end
