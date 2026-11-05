/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.DefectiveColor
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPath
public import LeanPool.GoldbergSeymour.ScheideDefectiveCrossingSelection
public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideDefectiveTerminalComponent
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumBoundaryFacts
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumUnused
public import LeanPool.GoldbergSeymour.ScheideExitVertex
public import LeanPool.GoldbergSeymour.ScheideExitVertices
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralInternalPair
public import LeanPool.GoldbergSeymour.ScheideSelectedBlockDeletion
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwapStable
public import LeanPool.GoldbergSeymour.TashkinovOrder
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePreservesTashkinovTree
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeUsedColors
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

public import LeanPool.GoldbergSeymour.TashkinovOrderBound

/-!
# Scheide Defective No Cross

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_htreeS_255.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let X : Finset V := TreeSequenceVertexSet T;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    ∀ (S : TreeSequence G e0), S.length + (2 : ℕ) = T.length → (
    ∀ (a : Fin C.p),
    ∃ (q : Fin (S.length + (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ S.vertex q = C.y a) → (
    ∀ (q : Fin S.length), (
    ∃ (a : Fin (C.p - (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ S.edge q = C.baseEdge a) ∨
    ∃ (r : Fin C.s) (j : Fin (2 : ℕ)), r ≠ i ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ S.edge q = C.blockEdge r
        j) → TashkinovTree G e0 phi T → Disjoint (DefectiveColors G phi (TreeSequenceVertexSet T))
        (TreeUsedColors phi T) ∧ Disjoint (TreeFreeColors phi T) (TreeUsedColors phi T) → (
    ∀ v ∈ X, (↑d : Fin k) ∉ MissingColors G phi v) → (
    ∀ (q : Fin T.length) (c : Fin k), phi (T.edge q) = some c → phi2 (T.edge q) = some c) → (
    ∀ v ∈ X,
    ∀ (c : Fin k), c ≠ gamma → c ≠ (↑d : Fin k) → (c ∈ MissingColors G phi2 v ↔ c ∈ MissingColors
        G phi v)) → TashkinovTree G e0 phi2 S := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i gamma X phi1 phi2 S hSlength hbaseVertices hedgeCases
      htreeOld hunused hdeltaNotMissing edge_color_phi2 missing_unaffected q hq
  rcases hedgeCases q with ⟨a, hqa, hqe⟩ | ⟨r, j, hri, hqbase, hqe⟩
  · have haPos : 1 ≤ a.val := by omega
    let oldq : Fin T.length := ⟨a.val, by omega⟩
    obtain ⟨b, c, hc, hm⟩ := htreeOld oldq haPos
    have hbP : b.val < C.p := by
      have hb := b.isLt
      dsimp [oldq] at hb
      omega
    let bp : Fin C.p := ⟨b.val, hbP⟩
    obtain ⟨bs, hbsval, hbs⟩ := hbaseVertices bp
    have hbq : b.val < q.val + 1 := by
      have hb := b.isLt
      dsimp [oldq] at hb
      omega
    let bn : Fin (q.val + 1) := ⟨b.val, hbq⟩
    have hcast : Fin.castLT bn
        (Nat.lt_trans bn.isLt (Nat.succ_lt_succ q.isLt)) = bs := by
      apply Fin.ext
      simpa [bn] using hbsval.symm
    have holdedge : T.edge oldq = C.baseEdge a := by
      simpa [oldq] using C.base_edge_position a
    have hcbase : phi (C.baseEdge a) = some c := holdedge ▸ hc
    have hcGamma : c ≠ gamma := by
      simpa [gamma, i] using C.initial_nonfirst_avoids_blocks a haPos c hcbase i
    have hcUsed : c ∈ TreeUsedColors phi T := by
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨oldq, haPos, hc⟩
    have hcDelta : c ≠ d.1 := by
      intro heq
      exact (Finset.disjoint_left.mp hunused.1) d.2 (heq ▸ hcUsed)
    refine ⟨bn, c, ?_, ?_⟩
    · rw [hqe]
      rw [← holdedge]
      exact edge_color_phi2 oldq c hc
    · rw [hcast, hbs]
      have hvbpX : C.y bp ∈ X := by
        rw [← C.base_vertex_position bp]
        simp [X, TreeSequenceVertexSet]
      have holdvertex : T.vertex
          (Fin.castLT b (Nat.lt_trans b.isLt (Nat.succ_lt_succ oldq.isLt))) =
          C.y bp := by
        have hidx : Fin.castLT b
            (Nat.lt_trans b.isLt (Nat.succ_lt_succ oldq.isLt)) =
            (⟨bp.val, by omega⟩ : Fin (T.length + 1)) := by
          apply Fin.ext
          rfl
        rw [hidx]
        exact C.base_vertex_position bp
      have hmBP : c ∈ MissingColors G phi (C.y bp) := by
        simpa only [holdvertex] using hm
      exact (missing_unaffected (C.y bp) hvbpX c hcGamma hcDelta).mpr hmBP
  · obtain ⟨b, hbmissing⟩ := C.block_color_missing_on_base r
    obtain ⟨bs, hbsval, hbs⟩ := hbaseVertices b
    let bn : Fin (q.val + 1) := ⟨b.val, by omega⟩
    have hcast : Fin.castLT bn
        (Nat.lt_trans bn.isLt (Nat.succ_lt_succ q.isLt)) = bs := by
      apply Fin.ext
      simpa [bn] using hbsval.symm
    have hrgamma : C.gamma r ≠ gamma := by
      intro h
      exact hri (C.gamma_injective (by simpa [gamma, i] using h))
    have hrdelta : C.gamma r ≠ d.1 := by
      intro h
      apply hdeltaNotMissing (C.y b)
      · rw [← C.base_vertex_position b]
        simp [X, TreeSequenceVertexSet]
      · exact h ▸ hbmissing
    let oldq : Fin T.length := ⟨C.p - 1 + 2 * r.val + j.val, by
      have hr := r.isLt
      have hj := j.isLt
      have hlen := C.length_eq
      omega⟩
    have holdedge : T.edge oldq = C.blockEdge r j := by
      simpa only [oldq] using C.block_edge_position r j
    have hcold : phi (T.edge oldq) = some (C.gamma r) := by
      rw [holdedge]
      exact C.block_color r j
    refine ⟨bn, C.gamma r, ?_, ?_⟩
    · rw [hqe]
      rw [← holdedge]
      exact edge_color_phi2 oldq (C.gamma r) hcold
    · rw [hcast, hbs]
      exact (missing_unaffected (C.y b) (by
        rw [← C.base_vertex_position b]
        simp [X, TreeSequenceVertexSet]) (C.gamma r) hrgamma hrdelta).mpr hbmissing

private theorem helper_adjoin_vertex_set_343.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] (G :
    LooplessMultigraph V E) (e0 : E) (A B : TreeSequence G e0) (f : E) (x y : V), G.ends f =
    s(x, y) → y ∉ TreeSequenceVertexSet A → TreeSequenceAdjoinEdge A f B →
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
    let j : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
    obtain ⟨a, ha⟩ := B.attaches j
    have hyEnds : y ∈ G.ends (B.edge j) := by
      rw [hlast, hxy]
      simp
    rw [ha] at hyEnds
    rcases (by simpa only [Sym2.mem_iff] using hyEnds) with hynew | hyold
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨j.succ, hynew.symm⟩
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt)),
        hyold.symm⟩
  have hinsert : insert y (TreeSequenceVertexSet A) ⊆ TreeSequenceVertexSet B := by
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

private theorem helper_tree_edge_incident_279.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E]
      (G : LooplessMultigraph V E) (e0 : E) (T : TreeSequence G e0) (q : Fin T.length),
    TreeIncidentEdge T (T.edge q) := by
  classical
  intro V E _ _ G e0 T q
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  obtain ⟨a, ha⟩ := T.attaches q
  refine ⟨T.vertex q.succ, ?_, ?_⟩
  · simp [TreeSequenceVertexSet]
  · simp [Incident, ha]

private theorem helper_component_vertex_of_edge_285.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let K : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ {v : V} {e : E}, Sum.inr e ∈ K → Incident G v e → phi1 e = some gamma ∨ phi1 e = some (↑d :
        Fin k) → Sum.inl v ∈ K := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i gamma phi1 K v e heK hve hecolor
  let H := TwoColorIncidenceGraph G phi1 gamma d.1
  have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
    simpa [H, TwoColorIncidenceGraph] using ⟨hve, hecolor⟩
  change H.connectedComponentMk (Sum.inr e) =
    H.connectedComponentMk (Sum.inl (D.v0 d)) at heK
  change H.connectedComponentMk (Sum.inl v) =
    H.connectedComponentMk (Sum.inl (D.v0 d))
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heK

private theorem helper_hz3v0_301.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    ∀ (g3 : E) (z3 w3 : V), D.v0 d ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex
        (D.gammaIndex d) (0 : Fin (2 : ℕ))) ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} :
        Finset V) : Finset V) → g3 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) (↑d : Fin
        k) → g3 ≠ D.f0 d → z3 ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d)
        (0 : Fin (2 : ℕ))) ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) :
        Finset V) → G.ends g3 = s(z3, w3) →
    let _ : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
        IsProperEdgeColoring G (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) →
        (
    ∀ (f : E), TreeIncidentEdge T f → OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex
        d)) f = phi f) → z3 ≠ D.v0 d := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d i gamma g3 z3 w3 hv0Z hg3B hg3f0 hz3Z hg3ends phi1 hproper1
      hfixed1 h
  have hboth := Finset.mem_sdiff.mp hz3Z
  have hv := Finset.mem_sdiff.mp hv0Z
  have hdeltaAtV0 : phi g3 = some d.1 := (Finset.mem_filter.mp hg3B).2
  have hphi1g3 : phi1 g3 = some d.1 := by
    apply (hfixed1 g3 ?_).trans hdeltaAtV0
    exact ⟨z3, hboth.1, by simp [Incident, hg3ends]⟩
  have hphi1f0 : phi1 (D.f0 d) = some d.1 := by
    apply (hfixed1 (D.f0 d) ?_).trans (D.f0_color d)
    exact ⟨D.v0 d, hv.1, by simp [Incident, D.f0_ends d]⟩
  have hproperBad : g3 = D.f0 d := by
    by_contra hne
    exact False.elim (hproper1 hne
      ⟨D.v0 d, by simpa [h] using
          (by simp [Incident, hg3ends] : Incident G z3 g3),
        by simp [Incident, D.f0_ends d]⟩ hphi1g3 hphi1f0)
  exact hg3f0 hproperBad

private theorem helper_hg1notK_326.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (g1 : E) (z1 : V),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    ∀ u1 ∈ TreeSequenceVertexSet T, G.ends g1 = s(u1, z1) →
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let K : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d)); (
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ↔ v = D.v0 d) → (
    ∀ {v : V} {e : E}, Sum.inr e ∈ K → Incident G v e → phi1 e = some gamma ∨ phi1 e = some (↑d :
        Fin k) → Sum.inl v ∈ K) → u1 ≠ D.v0 d → phi1 g1 = some (↑d : Fin k) → Sum.inr g1 ∉ K := by
  classical
  intro V E _ _ _ G k e0 phi T C D d g1 z1 i gamma u1 hu1X hg1ends phi1 K hKtree
      component_vertex_of_edge hu1v0 hphi1g1 hg1K
  have hu1g1 : Incident G u1 g1 := by
    change u1 ∈ G.ends g1
    rw [hg1ends]
    simp
  have hu1K := component_vertex_of_edge hg1K hu1g1 (Or.inr hphi1g1)
  exact hu1v0 ((hKtree u1 hu1X).mp hu1K)

private theorem helper_hg3notK_339.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    ∀ (g3 : E) (z3 w3 : V), z3 ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d)
        (0 : Fin (2 : ℕ))) ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) :
        Finset V) → G.ends g3 = s(z3, w3) →
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let K : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d)); (
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ↔ v = D.v0 d) → (
    ∀ {v : V} {e : E}, Sum.inr e ∈ K → Incident G v e → phi1 e = some gamma ∨ phi1 e = some (↑d :
        Fin k) → Sum.inl v ∈ K) → z3 ≠ D.v0 d → phi1 g3 = some (↑d : Fin k) → Sum.inr g3 ∉ K := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d i gamma g3 z3 w3 hz3Z hg3ends phi1 K hKtree
      component_vertex_of_edge hz3v0 hphi1g3 hg3K
  have hz3g3 : Incident G z3 g3 := by
    change z3 ∈ G.ends g3
    rw [hg3ends]
    simp
  have hz3K := component_vertex_of_edge hg3K hz3g3 (Or.inr hphi1g3)
  exact hz3v0 ((hKtree z3 (Finset.mem_sdiff.mp hz3Z).1).mp hz3K)

private theorem helper_hone2_351.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
        IsOneEdgeUncolored (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) e0 →
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d)); IsOneEdgeUncolored phi2 e0 := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i gamma phi1 K hone1 phi2
  constructor
  · have he0 : phi1 e0 = none := by simpa [phi1, gamma, i] using hone1.1
    simp [phi2, TwoColorComponentSwap, he0]
  · intro f hfe
    obtain ⟨c, hc⟩ := hone1.2 f hfe
    by_cases hfK' : Sum.inr f ∈ K
    · by_cases hcg : phi1 f = some gamma
      · exact ⟨d.1, by simp [phi2, TwoColorComponentSwap, K, hfK', hcg]⟩
      · by_cases hcd : phi1 f = some d.1
        · exact ⟨gamma, by simp [phi2, TwoColorComponentSwap, K, hfK', hcd]⟩
        · exact ⟨c, by simpa [phi2, TwoColorComponentSwap, K, hfK', hcg,
            hcd] using hc⟩
    · exact ⟨c, by simpa [phi2, TwoColorComponentSwap, K, hfK'] using hc⟩

private theorem helper_hdeltaNotMissing_397.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (d : ↥(DefectiveColors G
        phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (_ : TreeSequence G e0), ColoredVertexSetClosed G phi X →
    ∀ v ∈ X, (↑d : Fin k) ∉ MissingColors G phi v := by
  classical
  intro V E _ _ G k e0 phi T d X S hclosed v hv hm
  have hcard : 0 < (BoundaryColorEdges G phi X d.1).card := by
    have htwo : 2 ≤ (BoundaryColorEdges G phi X d.1).card := by
      have hdmem := d.2
      change d.1 ∈ (Finset.univ.filter fun alpha =>
        DefectiveColor G phi X alpha) at hdmem
      exact (Finset.mem_filter.mp hdmem).2
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hcard
  exact hclosed (Finset.mem_filter.mp hb).1 hv (Finset.mem_filter.mp hb).2 hm

private theorem helper_edge_color_phi2_408.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d)); (
    ∀ (f : E), TreeIncidentEdge T f → OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex
        d)) f = phi f) → (
    ∀ (q : Fin T.length), Sum.inr (T.edge q) ∉ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d))) → (
    ∀ (q : Fin T.length), TreeIncidentEdge T (T.edge q)) →
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    ∀ (q : Fin T.length) (c : Fin k), phi (T.edge q) = some c → phi2 (T.edge q) = some c := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i gamma phi1 K hfixed1 htreeEdgesOutside tree_edge_incident
      phi2 q c hc
  have hc1 : phi1 (T.edge q) = some c :=
    (hfixed1 _ (tree_edge_incident q)).trans hc
  have hout : Sum.inr (T.edge q) ∉ K := by
    simpa [K] using htreeEdgesOutside q
  simp [phi2, TwoColorComponentSwap, K, hout, hc1]

private theorem helper_hw3notS2_506.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
        ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    ∀ (u1 u2 w3 : V), u1 ∈ TreeSequenceVertexSet T → u2 ∈ TreeSequenceVertexSet T → w3 ∉
        TreeSequenceVertexSet T →
    ∀ (S : TreeSequence G e0), TreeSequenceVertexSet S = Z →
    ∀ (S1 : TreeSequence G e0), TreeSequenceVertexSet S1 = (insert u1 (TreeSequenceVertexSet S) :
        Finset V) →
    ∀ (S2 : TreeSequence G e0), TreeSequenceVertexSet S2 = (insert u2 (TreeSequenceVertexSet S1) :
        Finset V) → w3 ∉ TreeSequenceVertexSet S2 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d i X U Z u1 u2 w3 hu1X hu2X hw3X S hSverticesZ S1
      hS1vertices S2 hS2vertices
  rw [hS2vertices, hS1vertices]
  simp only [Finset.mem_insert, not_or]
  refine ⟨?_, ?_, ?_⟩
  · exact fun h => hw3X (h ▸ hu2X)
  · exact fun h => hw3X (h ▸ hu1X)
  · intro hwS
    apply hw3X
    rw [hSverticesZ] at hwS
    exact (Finset.mem_sdiff.mp hwS).1

private theorem helper_continuation_639.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (g1 : E) (z1 : V),
    let i : Fin C.s := D.gammaIndex d;
    let gamma : Fin k := C.gamma i;
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex i (0 : Fin (2 : ℕ)))
        ({C.blockVertex i (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    ∀ (u1 u2 : V) (g2 g3 : E) (z3 w3 : V) (_ : u1 ≠ u2) (_ : u1 ∈ TreeSequenceVertexSet T) (_ : u2
        ∈ TreeSequenceVertexSet T) (_ : G.ends g1 = s(u1, z1)) (_ : G.ends g2 = s(u1, u2)) (_ : z3
        ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V)) (_ : w3 ∉
        TreeSequenceVertexSet T) (_ : G.ends g3 = s(z3, w3)) (_ : z1 ∈ Z),
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    ∀ (_ : IsProperEdgeColoring G phi2) (_ : IsOneEdgeUncolored phi2 e0) (_ : (↑d : Fin k) ∈
        MissingColors G phi2 (D.v0 d)) (_ : D.alpha0 ∈ MissingColors G phi2 (C.y (⟨(0 : ℕ),
    by
                  first
                  | omega
                  | ( have := GoldbergSeymour.TreeSequence.positive T
                      have := C.p_ge_two
                      all_goals omega)
    ⟩ : Fin C.p))) (_ : phi2 g1 = some (↑d : Fin k)) (_ : phi2 g2 = some D.alpha0) (_ : phi2 g3 =
        some (↑d : Fin k)) (S : TreeSequence G e0) (_ : S.length + (2 : ℕ) = T.length) (_ :
        TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet
        T).card ∧ Odd (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)) (_ :
        TashkinovTree G e0 phi2 S) (_ :
    ∀ (A B : TreeSequence G e0) (f : E) (x y : V) (_ : G.ends f = s(x, y)) (_ : x ∈
        TreeSequenceVertexSet A) (_ : y ∉ TreeSequenceVertexSet A) (_ : TreeSequenceAdjoinEdge A f
        B), TreeSequenceVertexSet B = (insert y (TreeSequenceVertexSet A) : Finset V)) (_ :
        TreeSequenceVertexSet S = Z) (_ : D.v0 d ∈ TreeSequenceVertexSet S) (_ : C.y (⟨(0 : ℕ),
    by
                first
                | omega
                | ( have := GoldbergSeymour.TreeSequence.positive T
                    have := C.p_ge_two
                    all_goals omega)
    ⟩ : Fin C.p) ∈ TreeSequenceVertexSet S) (_ : u1 ∉ TreeSequenceVertexSet S) (_ : u2 ∉
        TreeSequenceVertexSet S), False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d g1 z1 i gamma X U Z u1 u2 g2 g3 z3 w3 hu12 hu1X hu2X
      hg1ends hg2ends hz3Z hw3X hg3ends hz1Z' phi1 phi2 hproper2 hone2 hdelta2 halpha02 hphi2g1
      hphi2g2 hphi2g3 S hSlength horder htreeS adjoin_vertex_set hSverticesZ hv0S hy0S hu1notS
      hu2notS
  have hz1S : z1 ∈ TreeSequenceVertexSet S := by
    rw [hSverticesZ]
    exact hz1Z'
  have hz3S : z3 ∈ TreeSequenceVertexSet S := by
    rw [hSverticesZ]
    exact hz3Z
  have hdeltaMissingS : d.1 ∈ TreeMissingColors phi2 S := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨D.v0 d, hv0S, hdelta2⟩
  have halphaMissingS : D.alpha0 ∈ TreeMissingColors phi2 S := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩,
      hy0S, halpha02⟩
  have hg1Boundary : g1 ∈ BoundaryEdges G (TreeSequenceVertexSet S) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z1, hz1S, u1, hu1notS, hg1ends.trans Sym2.eq_swap⟩
  obtain ⟨S1, hSS1⟩ := TreeSequenceBoundaryEdgeAppendExists S g1 hg1Boundary
  have hg1ends' : G.ends g1 = s(z1, u1) := by
    calc
      G.ends g1 = s(u1, z1) := hg1ends
      _ = s(z1, u1) := Sym2.eq_swap
  have hS1vertices : TreeSequenceVertexSet S1 =
      insert u1 (TreeSequenceVertexSet S) :=
    adjoin_vertex_set S S1 g1 z1 u1 hg1ends' hz1S hu1notS hSS1
  have haug1 : TashkinovAugmentation phi2 S S1 := by
    rcases hSS1 with ⟨hlen, hinit, hlast⟩
    exact ⟨hlen, hinit, d.1, (congrArg phi2 hlast).trans hphi2g1,
      hdeltaMissingS⟩
  have htreeS1 : TashkinovTree G e0 phi2 S1 :=
    TashkinovAugmentationSequencePreservesTashkinovTree G e0 phi2 S S1
      htreeS (Relation.ReflTransGen.single haug1)
  have hu1S1 : u1 ∈ TreeSequenceVertexSet S1 := by simp [hS1vertices]
  have hu2notS1 : u2 ∉ TreeSequenceVertexSet S1 := by
    rw [hS1vertices]
    simp [hu12.symm, hu2notS]
  have hy0S1 : C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈
      TreeSequenceVertexSet S1 := by
    rw [hS1vertices]
    exact Finset.mem_insert_of_mem hy0S
  have halphaMissingS1 : D.alpha0 ∈ TreeMissingColors phi2 S1 := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨_, hy0S1, halpha02⟩
  have hg2Boundary : g2 ∈ BoundaryEdges G (TreeSequenceVertexSet S1) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u1, hu1S1, u2, hu2notS1, hg2ends⟩
  obtain ⟨S2, hS1S2⟩ := TreeSequenceBoundaryEdgeAppendExists S1 g2 hg2Boundary
  have hS2vertices : TreeSequenceVertexSet S2 =
      insert u2 (TreeSequenceVertexSet S1) :=
    adjoin_vertex_set S1 S2 g2 u1 u2 hg2ends hu1S1 hu2notS1 hS1S2
  have haug2 : TashkinovAugmentation phi2 S1 S2 := by
    rcases hS1S2 with ⟨hlen, hinit, hlast⟩
    exact ⟨hlen, hinit, D.alpha0, (congrArg phi2 hlast).trans hphi2g2,
      halphaMissingS1⟩
  have htreeS2 : TashkinovTree G e0 phi2 S2 :=
    TashkinovAugmentationSequencePreservesTashkinovTree G e0 phi2 S1 S2
      htreeS1 (Relation.ReflTransGen.single haug2)
  have hz3S2 : z3 ∈ TreeSequenceVertexSet S2 := by
    rw [hS2vertices, hS1vertices]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz3S)
  have hw3notS2 : w3 ∉ TreeSequenceVertexSet S2 := by
    exact @helper_hw3notS2_506 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@u1) (@u2) (@w3) (@hu1X) (@hu2X) (@hw3X) (@S)
        (@hSverticesZ) (@S1) (@hS1vertices) (@S2) (@hS2vertices)
  have hv0S2 : D.v0 d ∈ TreeSequenceVertexSet S2 := by
    rw [hS2vertices, hS1vertices]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv0S)
  have hdeltaMissingS2 : d.1 ∈ TreeMissingColors phi2 S2 := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨D.v0 d, hv0S2, hdelta2⟩
  have hg3Boundary : g3 ∈ BoundaryEdges G (TreeSequenceVertexSet S2) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z3, hz3S2, w3, hw3notS2, hg3ends⟩
  obtain ⟨S3, hS2S3⟩ := TreeSequenceBoundaryEdgeAppendExists S2 g3 hg3Boundary
  have hS3vertices : TreeSequenceVertexSet S3 =
      insert w3 (TreeSequenceVertexSet S2) :=
    adjoin_vertex_set S2 S3 g3 z3 w3 hg3ends hz3S2 hw3notS2 hS2S3
  have haug3 : TashkinovAugmentation phi2 S2 S3 := by
    rcases hS2S3 with ⟨hlen, hinit, hlast⟩
    exact ⟨hlen, hinit, d.1, (congrArg phi2 hlast).trans hphi2g3,
      hdeltaMissingS2⟩
  have htreeS3 : TashkinovTree G e0 phi2 S3 :=
    TashkinovAugmentationSequencePreservesTashkinovTree G e0 phi2 S2 S3
      htreeS2 (Relation.ReflTransGen.single haug3)
  have hK2 : KTriple G k e0 phi2 :=
    ⟨C.globally_maximum.1.1, C.globally_maximum.1.2.1,
      C.globally_maximum.1.2.2.1, hproper2, hone2⟩
  have hle := treeCard_le_tashkinovOrder G k e0 phi2 S3 hK2 htreeS3
  have hS3card : (TreeSequenceVertexSet S3).card = S3.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      S3.vertex_injective]
  have hXcard : X.card = T.length + 1 := by
    simp [X, TreeSequenceVertexSet, Finset.card_image_of_injective,
      T.vertex_injective]
  rcases hSS1 with ⟨hlen1, hinit1, hlast1⟩
  rcases hS1S2 with ⟨hlen2, hinit2, hlast2⟩
  rcases hS2S3 with ⟨hlen3, hinit3, hlast3⟩
  have hmore : (TreeSequenceVertexSet S3).card = X.card + 1 := by
    rw [hS3card, hXcard]
    omega
  rw [hmore, horder.1] at hle
  exact (Nat.not_succ_le_self X.card) hle

theorem ScheideDefectiveNoCross {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
    ∀ f : E, phi f = some d.1 → ¬ (
    ∃ x ∈ ({C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} : Finset V),
        Incident G x f ∧
    ∃ z ∈ TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}, Incident G z f) := by
  classical
  intro d g1 hg1
  rintro ⟨x, hxU, hxg1, z1, hz1Z, hz1g1⟩
  let i := D.gammaIndex d
  let gamma := C.gamma i
  let X := TreeSequenceVertexSet T
  let U := ({C.blockVertex i 0, C.blockVertex i 1} : Finset V)
  let Z := X \ U
  have hselection := ScheideDefectiveCrossingSelection G k e0 phi T C D d
    g1 hg1 x hxU hxg1 z1 hz1Z hz1g1
  dsimp only at hselection
  rcases hselection with
    ⟨u1, u2, g2, g3, z3, w3, hpair, hxu1, hu12, hu1U, hu2U, hu1X,
      hu2X, hv0Z, hy0Z, hagamma, hadelta, hgammadelta, hg1ends,
      hg2color, hg2ends, hg3B, hg3f0, hz3Z, hw3X, hg3ends,
      hg1g2, hg1g3, hg2g3⟩
  have hz1Z' : z1 ∈ Z := by simpa [i, X, U, Z] using hz1Z
  let phi1 := OutsideTreeColorSwap T phi D.alpha0 gamma
  let K := TwoColorComponent G phi1 gamma d.1 (Sum.inl (D.v0 d))
  have hterminal := ScheideDefectiveTerminalComponent G k e0 phi T C D d
  dsimp only at hterminal
  rcases hterminal with
    ⟨hproper1, hone1, hstable1, hfixed1, htailK, hf0K, hKtree,
      htreeEdgesOutside, hKcolors⟩
  have tree_edge_incident : ∀ q : Fin T.length, TreeIncidentEdge T (T.edge q) := by
    exact @helper_tree_edge_incident_279 (@V) (@E) inferInstance inferInstance (@G) (@e0) (@T)
  have component_vertex_of_edge {v : V} {e : E}
      (heK : Sum.inr e ∈ K) (hve : Incident G v e)
      (hecolor : phi1 e = some gamma ∨ phi1 e = some d.1) :
      Sum.inl v ∈ K := by
    exact @helper_component_vertex_of_edge_285 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@v) (@e) (@heK) (@hve) (@hecolor)
  have hu1v0 : u1 ≠ D.v0 d := by
    intro h
    have : D.v0 d ∈ U := h ▸ hu1U
    exact (Finset.mem_sdiff.mp hv0Z).2 this
  have hz3v0 : z3 ≠ D.v0 d := by
    exact @helper_hz3v0_301 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@g3) (@z3) (@w3) (@hv0Z) (@hg3B) (@hg3f0)
        (@hz3Z) (@hg3ends) (@hproper1) (@hfixed1)
  have hphi1g1 : phi1 g1 = some d.1 := by
    exact (hfixed1 g1 ⟨u1, hu1X, by simp [Incident, hg1ends]⟩).trans hg1
  have hphi1g2 : phi1 g2 = some D.alpha0 := by
    exact (hfixed1 g2 ⟨u1, hu1X, by simp [Incident, hg2ends]⟩).trans hg2color
  have hphi1g3 : phi1 g3 = some d.1 := by
    exact (hfixed1 g3 ⟨z3, (Finset.mem_sdiff.mp hz3Z).1,
      by simp [Incident, hg3ends]⟩).trans (Finset.mem_filter.mp hg3B).2
  have hg1notK : Sum.inr g1 ∉ K := by
    exact @helper_hg1notK_326 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@C) (@D) (@d) (@g1) (@z1) (@u1) (@hu1X) (@hg1ends) (@hKtree)
        (@component_vertex_of_edge) (@hu1v0) (@hphi1g1)
  have hg2notK : Sum.inr g2 ∉ K := by
    intro hg2K
    rcases hKcolors g2 hg2K with hgamma | hdelta
    · exact hagamma (Option.some.inj (hphi1g2.symm.trans hgamma))
    · exact hadelta (Option.some.inj (hphi1g2.symm.trans hdelta))
  have hg3notK : Sum.inr g3 ∉ K := by
    exact @helper_hg3notK_339 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@g3) (@z3) (@w3) (@hz3Z) (@hg3ends) (@hKtree)
        (@component_vertex_of_edge) (@hz3v0) (@hphi1g3)
  let phi2 := TwoColorComponentSwap G phi1 gamma d.1 (Sum.inl (D.v0 d))
  have hproper2 : IsProperEdgeColoring G phi2 := by
    simpa [phi2] using TwoColorComponentSwapProper G phi1 gamma d.1
      hgammadelta hproper1 (Sum.inl (D.v0 d))
  have hone2 : IsOneEdgeUncolored phi2 e0 := by
    exact @helper_hone2_351 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@C) (@D) (@d) (@hone1)
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi1 gamma d.1
    hgammadelta hproper1 (Sum.inl (D.v0 d))
  have hv0X : D.v0 d ∈ X := (Finset.mem_sdiff.mp hv0Z).1
  have hy0X : C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈ X :=
    (Finset.mem_sdiff.mp hy0Z).1
  have hgamma1 : gamma ∈ MissingColors G phi1 (D.v0 d) := by
    rw [hstable1.2 (D.v0 d) (by simpa [X] using hv0X)]
    exact D.gamma_missing_at_v0 d
  have hdelta2 : d.1 ∈ MissingColors G phi2 (D.v0 d) := by
    simpa [phi2, K] using hbehavior.2.1 (D.v0 d) (by rfl) hgamma1
  have halpha01 : D.alpha0 ∈ MissingColors G phi1
      (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩) := by
    rw [hstable1.2 _ (by simpa [X] using hy0X)]
    exact D.alpha0_missing_at_y0
  have halpha02 : D.alpha0 ∈ MissingColors G phi2
      (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩) := by
    exact (hbehavior.2.2.2 _ D.alpha0 hagamma hadelta).mpr halpha01
  have hphi2g1 : phi2 g1 = some d.1 := by
    simp [phi2, TwoColorComponentSwap, K, hg1notK, hphi1g1]
  have hphi2g2 : phi2 g2 = some D.alpha0 := by
    simp [phi2, TwoColorComponentSwap, K, hg2notK, hphi1g2]
  have hphi2g3 : phi2 g3 = some d.1 := by
    simp [phi2, TwoColorComponentSwap, K, hg3notK, hphi1g3]
  obtain ⟨S, hSvertices, hSlength, hvertexReindex, hedgeReindex,
    hbaseVertices, hbaseEdges, hblockEntries, hedgeCases, hedgeOld,
    hnotIncident⟩ :=
    ScheideSelectedBlockDeletion G k e0 phi T C i
  have htreeOld : TashkinovTree G e0 phi T := C.globally_maximum.2.1
  have hunused := ScheideGlobalMaximumUnused G k e0 phi T C.globally_maximum
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact horder.2.2.2.2
  have hdeltaNotMissing : ∀ v, v ∈ X → d.1 ∉ MissingColors G phi v := by
    exact @helper_hdeltaNotMissing_397 (@V) (@E) inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@d) (@S) (@hclosed)
  have edge_color_phi2 (q : Fin T.length) (c : Fin k)
      (hc : phi (T.edge q) = some c) : phi2 (T.edge q) = some c := by
    exact @helper_edge_color_phi2_408 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@hfixed1) (@htreeEdgesOutside)
        (@tree_edge_incident) (@q) (@c) (@hc)
  have missing_unaffected (v : V) (hvX : v ∈ X) (c : Fin k)
      (hcg : c ≠ gamma) (hcd : c ≠ d.1) :
      (c ∈ MissingColors G phi2 v ↔ c ∈ MissingColors G phi v) := by
    have h1 : MissingColors G phi1 v = MissingColors G phi v :=
      hstable1.2 v (by simpa [X] using hvX)
    rw [← h1]
    exact hbehavior.2.2.2 v c hcg hcd
  have htreeS : TashkinovTree G e0 phi2 S := by
    exact @helper_htreeS_255 V E inferInstance inferInstance inferInstance G k e0 phi T C D d S
        hSlength hbaseVertices hedgeCases htreeOld hunused hdeltaNotMissing edge_color_phi2
        missing_unaffected
  have adjoin_vertex_set (A B : TreeSequence G e0) (f : E) (x y : V)
      (hxy : G.ends f = s(x, y)) (hxA : x ∈ TreeSequenceVertexSet A)
      (hyA : y ∉ TreeSequenceVertexSet A)
      (hAB : TreeSequenceAdjoinEdge A f B) :
      TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A) := by
    exact @helper_adjoin_vertex_set_343 V E inferInstance G e0 A B f x y hxy hyA hAB
  have hSverticesZ : TreeSequenceVertexSet S = Z := by
    simpa [Z, X, U, i] using hSvertices
  have hv0S : D.v0 d ∈ TreeSequenceVertexSet S := by
    rw [hSverticesZ]
    exact hv0Z
  have hy0S : C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈
      TreeSequenceVertexSet S := by
    rw [hSverticesZ]
    exact hy0Z
  have hu1notS : u1 ∉ TreeSequenceVertexSet S := by
    rw [hSverticesZ]
    exact fun h => (Finset.mem_sdiff.mp h).2 hu1U
  have hu2notS : u2 ∉ TreeSequenceVertexSet S := by
    rw [hSverticesZ]
    exact fun h => (Finset.mem_sdiff.mp h).2 hu2U
  exact @helper_continuation_639 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@g1) (@z1) (@u1) (@u2) (@g2)
      (@g3) (@z3) (@w3) (@hu12) (@hu1X) (@hu2X) (@hg1ends) (@hg2ends) (@hz3Z) (@hw3X) (@hg3ends)
      (@hz1Z') (@hproper2) (@hone2) (@hdelta2) (@halpha02) (@hphi2g1) (@hphi2g2) (@hphi2g3) (@S)
      (@hSlength) (@horder) (@htreeS) (@adjoin_vertex_set) (@hSverticesZ) (@hv0S) (@hy0S)
      (@hu1notS) (@hu2notS)
end GoldbergSeymour

end
