/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module


public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideDefectiveSwitchEffect
public import LeanPool.GoldbergSeymour.ScheideReplacementBoundaryParity

/-!
# Scheide Replacement Boundary At Most Three

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hout_ne_132.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    ∀ (g1 g2 : E), g2 ≠ g1 → (g1 ∈ BoundaryColorEdges G phi Z (↑d : Fin k) ∧
    ∃ w ∉ X, Incident G w g1) → (g2 ∈ BoundaryColorEdges G phi Z (↑d : Fin k) ∧
    ∃ w ∉ X, Incident G w g2) →
    ∀ (w1 : V), Incident G w1 g1 →
    ∀ (w2 : V), Incident G w2 g2 → IsProperEdgeColoring G phi → w1 ≠ w2 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X U Z g1 g2 hg2g1 hg1data hg2data w1 hw1g w2 hw2g hproper h
  have hadj : AdjacentEdges G g1 g2 := ⟨w1, hw1g, by simpa [h] using hw2g⟩
  have hfc : phi g1 = some d.1 := by
    exact (Finset.mem_filter.mp hg1data.1).2
  have hgc : phi g2 = some d.1 := by
    exact (Finset.mem_filter.mp hg2data.1).2
  exact hproper (Ne.symm hg2g1) hadj hfc hgc

private theorem helper_hdeltaNotMissing_146.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (_ : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (_ _ : E) (_ : TreeSequence G e0),
    ∀ v ∈ X, (↑d : Fin k) ∉ MissingColors G phi v := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X g1 g2 S v hv hm
  have hclosed : ColoredVertexSetClosed G phi X :=
    (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (BoundaryColorEdges G phi X d.1).card by
    have hd := d.2
    change d.1 ∈ Finset.univ.filter (fun c => DefectiveColor G phi X c) at hd
    have := (Finset.mem_filter.mp hd).2
    change 2 ≤ (BoundaryColorEdges G phi X d.1).card at this
    omega)
  exact hclosed (Finset.mem_filter.mp hb).1 hv (Finset.mem_filter.mp hb).2 hm

private theorem helper_edge_color_D_163.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))), (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → f ≠ D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f) →
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); (
    ∀ (q : Fin T.length), TreeIncidentEdge T (T.edge q)) →
    ∀ (q : Fin T.length) (c : Fin k), phi (T.edge q) = some c → phiD (T.edge q) = some c := by
  classical
  intro V E _ _ _ G k e0 phi T C D d hfixD phiD tree_edge_incident q c hc
  have hf := hfixD (T.edge q) (tree_edge_incident q)
  calc
    phiD (T.edge q) = phi (T.edge q) := by
      apply hf
      intro he
      obtain ⟨a, ha⟩ := T.attaches q
      have hu : D.u0 d ∈ G.ends (T.edge q) := by
        rw [he, D.f0_ends]
        simp
      rw [ha] at hu
      rcases Sym2.mem_iff.mp hu with hu | hu
      · exact D.u0_outside d (by
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨q.succ, hu.symm⟩)
      · exact D.u0_outside d (by
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)), hu.symm⟩)
    _ = some c := hc

private theorem helper_missing_unaffected_183.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T; MissingColors G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (D.v0 d) = (insert (↑d : Fin
        k) ((MissingColors G phi (D.v0 d)).erase (C.gamma (D.gammaIndex d))) : Finset (Fin k)) → (
    ∀ v ∈ TreeSequenceVertexSet T, v ≠ D.v0 d → MissingColors G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) →
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ v ∈ X,
    ∀ (c : Fin k), c ≠ C.gamma (D.gammaIndex d) → c ≠ (↑d : Fin k) → (c ∈ MissingColors G phiD v ↔
        c ∈ MissingColors G phi v) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X hmissD htreeD phiD v hv c hc hd
  by_cases hv0 : v = D.v0 d
  · subst v
    rw [hmissD]
    simp [hc, hd]
  · rw [htreeD v hv hv0]

private theorem helper_htreeS_191.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (_ _ : E),
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ (S : TreeSequence G e0), S.length + (2 : ℕ) = T.length → (
    ∀ (a : Fin C.p),
    ∃ (q : Fin (S.length + (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ S.vertex q = C.y a) → (
    ∀ (q : Fin S.length), (
    ∃ (a : Fin (C.p - (1 : ℕ))), (↑q : ℕ) = (↑a : ℕ) ∧ S.edge q = C.baseEdge a) ∨
    ∃ (r : Fin C.s) (j : Fin (2 : ℕ)), r ≠ D.gammaIndex d ∧ C.p - (1 : ℕ) ≤ (↑q : ℕ) ∧ S.edge q =
        C.blockEdge r j) → TashkinovTree G e0 phi T → Disjoint (DefectiveColors G phi
        (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧ Disjoint (TreeFreeColors phi T)
        (TreeUsedColors phi T) → (
    ∀ v ∈ X, (↑d : Fin k) ∉ MissingColors G phi v) → (
    ∀ (q : Fin T.length) (c : Fin k), phi (T.edge q) = some c → phiD (T.edge q) = some c) → (
    ∀ v ∈ X,
    ∀ (c : Fin k), c ≠ C.gamma (D.gammaIndex d) → c ≠ (↑d : Fin k) → (c ∈ MissingColors G phiD v ↔
        c ∈ MissingColors G phi v)) → TashkinovTree G e0 phiD S := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X g1 g2 phiD S hSlength hbaseVertices hedgeCases htreeOld
      hunused hdeltaNotMissing edge_color_D missing_unaffected q hq
  rcases hedgeCases q with ⟨a, hqa, hqe⟩ | ⟨r, j, hri, hqbase, hqe⟩
  · have haPos : 1 ≤ a.val := by omega
    have hlen := C.length_eq
    have hi := (D.gammaIndex d).isLt
    let oldq : Fin T.length := ⟨a.val, by omega⟩
    obtain ⟨b, c, hc, hm⟩ := htreeOld oldq haPos
    have ha := a.isLt
    have hb := b.isLt
    have hb0 : b.val < oldq.val + 1 := hb
    have hbP : b.val < C.p := by
      have haP : a.val < C.p - 1 := a.isLt
      change b.val < a.val + 1 at hb0
      omega
    let bp : Fin C.p := ⟨b.val, hbP⟩
    obtain ⟨bs, hbsval, hbs⟩ := hbaseVertices bp
    have hl := C.length_eq
    have hq := q.isLt
    let bn : Fin (q.val + 1) := ⟨b.val, by
      have hb := b.isLt
      have hqa' : q.val = a.val := hqa
      change b.val < a.val + 1 at hb
      omega⟩
    have hcast : Fin.castLT bn
        (Nat.lt_trans bn.isLt (Nat.succ_lt_succ q.isLt)) = bs := by
      apply Fin.ext
      simpa [bn] using hbsval.symm
    have holdedge : T.edge oldq = C.baseEdge a := by
      simpa [oldq] using C.base_edge_position a
    have hcbase : phi (C.baseEdge a) = some c := holdedge ▸ hc
    have hcGamma : c ≠ C.gamma (D.gammaIndex d) := by
      simpa using C.initial_nonfirst_avoids_blocks a haPos c hcbase (D.gammaIndex d)
    have hcDelta : c ≠ d.1 := by
      intro heq
      exact (Finset.disjoint_left.mp hunused.1) d.2 (heq ▸ (by
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨oldq, haPos, hc⟩))
    refine ⟨bn, c, ?_, ?_⟩
    · rw [hqe, ← holdedge]
      exact edge_color_D oldq c hc
    · rw [hcast, hbs]
      have hvbpX : C.y bp ∈ X := by
        rw [← C.base_vertex_position bp]
        simp [X, TreeSequenceVertexSet]
      have holdvertex : T.vertex
          (Fin.castLT b (Nat.lt_trans b.isLt (Nat.succ_lt_succ oldq.isLt))) = C.y bp := by
        have hi : Fin.castLT b (Nat.lt_trans b.isLt (Nat.succ_lt_succ oldq.isLt)) =
            (⟨bp.val, by omega⟩ : Fin (T.length + 1)) := by apply Fin.ext; rfl
        rw [hi]
        exact C.base_vertex_position bp
      apply (missing_unaffected (C.y bp) hvbpX c hcGamma hcDelta).mpr
      simpa [holdvertex] using hm
  · obtain ⟨b, hbmissing⟩ := C.block_color_missing_on_base r
    obtain ⟨bs, hbsval, hbs⟩ := hbaseVertices b
    let bn : Fin (q.val + 1) := ⟨b.val, by omega⟩
    have hcast : Fin.castLT bn (Nat.lt_trans bn.isLt (Nat.succ_lt_succ q.isLt)) = bs := by
      apply Fin.ext
      simpa [bn] using hbsval.symm
    have hrgamma : C.gamma r ≠ C.gamma (D.gammaIndex d) := by
      intro h
      exact hri (C.gamma_injective (by simpa using h))
    have hrdelta : C.gamma r ≠ d.1 := by
      intro h
      apply hdeltaNotMissing (C.y b)
      · rw [← C.base_vertex_position b]
        simp [X, TreeSequenceVertexSet]
      · exact h ▸ hbmissing
    let oldq : Fin T.length := ⟨C.p - 1 + 2 * r.val + j.val, by
      have hl := C.length_eq
      omega⟩
    have holdedge : T.edge oldq = C.blockEdge r j := by
      simpa [oldq] using C.block_edge_position r j
    have hcold : phi (T.edge oldq) = some (C.gamma r) := by
      rw [holdedge]
      exact C.block_color r j
    refine ⟨bn, C.gamma r, ?_, ?_⟩
    · rw [hqe, ← holdedge]
      exact edge_color_D oldq (C.gamma r) hcold
    · rw [hcast, hbs]
      exact (missing_unaffected (C.y b) (by
        rw [← C.base_vertex_position b]
        simp [X, TreeSequenceVertexSet]) (C.gamma r) hrgamma hrdelta).mpr hbmissing

private theorem helper_adjoin_set_312.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (_ : ScheideDefectiveSetup G k e0 phi
        T C) (_ : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (_ _ : E) (_ A B :
        TreeSequence G e0) (f : E) (x y : V), G.ends f = s(x, y) → y ∉ TreeSequenceVertexSet A →
        TreeSequenceAdjoinEdge A f B → TreeSequenceVertexSet B = (insert y (TreeSequenceVertexSet
        A) : Finset V) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d g1 g2 S A B f x y hxy hy hab
  rcases hab with ⟨hlen, hinit, hlast⟩
  have sub : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨i, hi⟩ := hv
    exact ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, hinit.2.1 i ▸ hi⟩
  have hyB : y ∈ TreeSequenceVertexSet B := by
    let j : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
    obtain ⟨i, hi⟩ := B.attaches j
    have hm : y ∈ G.ends (B.edge j) := by rw [hlast, hxy]; simp
    rw [hi] at hm
    rcases (by simpa only [Sym2.mem_iff] using hm) with hm | hm
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]; exact
        ⟨j.succ, hm.symm⟩
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)), hm.symm⟩
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hyB
    · exact sub hv
  · have hy' : y ∉ Finset.image A.vertex Finset.univ := by
      simpa [TreeSequenceVertexSet] using hy
    have hca : (TreeSequenceVertexSet A).card = A.length + 1 := by
      simp [TreeSequenceVertexSet, Finset.card_image_of_injective, A.vertex_injective]
    have hcb : (TreeSequenceVertexSet B).card = B.length + 1 := by
      simp [TreeSequenceVertexSet, Finset.card_image_of_injective, B.vertex_injective]
    rw [hcb]
    rw [Finset.card_insert_of_notMem hy]
    rw [hca]
    omega

private theorem helper_htreeS2_381.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    ∀ (g2 : E), g2 ≠ D.f0 d → (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → f ≠ D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f) →
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); (g2 ∈ BoundaryColorEdges G phi Z (↑d : Fin k) ∧
    ∃ w ∉ X, Incident G w g2) →
    ∀ z2 ∈ Z,
    ∀ (w2 : V), G.ends g2 = s(z2, w2) →
    ∀ (S1 : TreeSequence G e0), TashkinovTree G e0 phiD S1 →
    ∀ (S2 : TreeSequence G e0), TreeSequenceAdjoinEdge S1 g2 S2 → (↑d : Fin k) ∈ TreeMissingColors
        phiD S1 → TashkinovTree G e0 phiD S2 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X U Z g2 hg2f0 hfixD phiD hg2data z2 hz2Z w2 he2 S1
      htreeS1 S2 hS2 d_missing_S1
  apply TashkinovAugmentationSequencePreservesTashkinovTree G e0 phiD S1 S2 htreeS1
  rcases hS2 with ⟨hlen, hinit, hlast⟩
  exact Relation.ReflTransGen.single ⟨hlen, hinit, d.1,
    (congrArg phiD hlast).trans (by
      have hf := hfixD g2
        (show ∃ v ∈ TreeSequenceVertexSet T, Incident G v g2 from
          ⟨z2, (Finset.mem_sdiff.mp hz2Z).1, by
            change z2 ∈ G.ends g2
            rw [he2]
            simp⟩) hg2f0
      calc
        phiD g2 = phi g2 := by simpa [phiD] using hf
        _ = some d.1 := (Finset.mem_filter.mp hg2data.1).2),
    d_missing_S1⟩

private theorem helper_hw3S2_399.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] (G : LooplessMultigraph V E) (e0 : E) (w1 w2
        w3 : V) (S S1 : TreeSequence G e0), w3 ∉ TreeSequenceVertexSet S → w1 ≠ w3 → w3 ≠ w2 →
        TreeSequenceVertexSet S1 = (insert w1 (TreeSequenceVertexSet S) : Finset V) →
    ∀ (S2 : TreeSequence G e0), TreeSequenceVertexSet S2 = (insert w2 (TreeSequenceVertexSet S1) :
        Finset V) → w3 ∉ TreeSequenceVertexSet S2 := by
  classical
  intro V E _ G e0 w1 w2 w3 S S1 hw3S hout_ne13 hout_ne23 hS1set S2 hS2set
  rw [hS2set]
  simp only [Finset.mem_insert, not_or]
  exact ⟨hout_ne23, by
    intro h
    rw [hS1set] at h
    rcases Finset.mem_insert.mp h with h | h
    · exact hout_ne13.symm h
    · exact hw3S h⟩

private theorem helper_htreeS3_424.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    ∀ (g3 : E), g3 ≠ D.f0 d → (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → f ≠ D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f) →
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d)); (g3 ∈ BoundaryColorEdges G phi Z (↑d : Fin k) ∧
    ∃ w ∉ X, Incident G w g3) →
    ∀ z3 ∈ Z,
    ∀ (w3 : V), G.ends g3 = s(z3, w3) →
    ∀ (S2 : TreeSequence G e0), TashkinovTree G e0 phiD S2 → (↑d : Fin k) ∈ TreeMissingColors phiD
        S2 →
    ∀ (S3 : TreeSequence G e0), TreeSequenceAdjoinEdge S2 g3 S3 → TashkinovTree G e0 phiD S3 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X U Z g3 hg3f0 hfixD phiD hg3data z3 hz3Z w3 he3 S2
      htreeS2 d_missing_S2 S3 hS3
  apply TashkinovAugmentationSequencePreservesTashkinovTree G e0 phiD S2 S3 htreeS2
  rcases hS3 with ⟨hlen, hinit, hlast⟩
  exact Relation.ReflTransGen.single ⟨hlen, hinit, d.1,
    (congrArg phiD hlast).trans (by
      have hf := hfixD g3
        (show ∃ v ∈ TreeSequenceVertexSet T, Incident G v g3 from
          ⟨z3, (Finset.mem_sdiff.mp hz3Z).1, by
            change z3 ∈ G.ends g3
            rw [he3]
            simp⟩) hg3f0
      calc
        phiD g3 = phi g3 := by simpa [phiD] using hf
        _ = some d.1 := (Finset.mem_filter.mp hg3data.1).2),
    d_missing_S2⟩

private theorem helper_hle_439.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (_ _ : E),
        IsProperEdgeColoring G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin
        k) (Sum.inl (D.v0 d))) → IsOneEdgeUncolored (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) e0 →
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ (_ S3 : TreeSequence G e0), TashkinovTree G e0 phiD S3 → (TreeSequenceVertexSet S3).card ≤
        TashkinovOrder G := by
  classical
  intro V E _ _ _ G k e0 phi T C D d g1 g2 hproperD honeD phiD S S3 htreeS3
  unfold TashkinovOrder
  dsimp
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (by
    simp only [Finset.mem_filter, Finset.mem_range]
    have hk : ChromaticIndex G - 1 = k := by
      have hh := C.globally_maximum.1.2.1
      omega
    rw [hk]
    refine ⟨?_, e0, phiD, S3, ?_, htreeS3, rfl⟩
    · have hV : (TreeSequenceVertexSet S3).card ≤ Fintype.card V := by
        simpa using Finset.card_le_card (Finset.subset_univ (TreeSequenceVertexSet S3))
      omega
    · exact ⟨C.globally_maximum.1.1, C.globally_maximum.1.2.1,
        C.globally_maximum.1.2.2.1, hproperD, honeD⟩)

private theorem helper_continuation_668.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let U : Finset V := (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    let B : Finset E := ({f ∈ BoundaryColorEdges G phi Z (↑d : Fin k) |
    ∃ w ∉ X, Incident G w f} : Finset E);
    ∀ (_ : D.v0 d ∈ Z ∧ C.y (⟨(0 : ℕ),
    by
                    first
                    | omega
                    | ( have := GoldbergSeymour.TreeSequence.positive T
                        have :=
                          GoldbergSeymour.ScheideStructuralConfiguration.p_ge_two
                            (ScheideReducedConfiguration.toScheideStructuralConfiguration
                            C)
                        all_goals omega)
    ⟩ : Fin C.p) ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ))) ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V) ∧ (
    ∀ z ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V),
    ∃! f : E, Incident G z f ∧ phi f = some (↑d : Fin k)) ∧ D.f0 d ∈ B ∧ Odd B.card) (g1 g2 : E)
        (_ : g2 ≠ D.f0 d) (g3 : E) (_ : g3 ≠ D.f0 d) (_ : g3 ≠ g1) (_ : g3 ≠ g2) (_ :
        IsProperEdgeColoring G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin
        k) (Sum.inl (D.v0 d)))) (_ : IsOneEdgeUncolored (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) e0) (_ : MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (D.v0 d) = (insert (↑d : Fin k) ((MissingColors G phi (D.v0 d)).erase (C.gamma
        (D.gammaIndex d))) : Finset (Fin k))) (_ :
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → f ≠ D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f),
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d))
        (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ (_ : g1 ∈ BoundaryColorEdges G phi Z (↑d : Fin k) ∧
    ∃ w ∉ X, Incident G w g1) (_ : g2 ∈ BoundaryColorEdges G phi Z (↑d : Fin k) ∧
    ∃ w ∉ X, Incident G w g2) (_ : g3 ∈ BoundaryColorEdges G phi Z (↑d : Fin k) ∧
    ∃ w ∉ X, Incident G w g3) (z1 z2 : V) (_ : z2 ∈ Z) (z3 : V) (_ : z3 ∈ Z) (w1 : V) (_ : w1 ∉ X)
        (_ : Incident G w1 g1) (w2 : V) (_ : w2 ∉ X) (_ : Incident G w2 g2) (w3 : V) (_ : w3 ∉ X)
        (_ : Incident G w3 g3) (_ : G.ends g1 = s(z1, w1)) (_ : G.ends g2 = s(z2, w2)) (_ : G.ends
        g3 = s(z3, w3)) (_ : IsProperEdgeColoring G phi) (_ : w1 ≠ w2) (S : TreeSequence G e0) (_
        : TreeSequenceVertexSet S = TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex
        d) (0 : Fin (2 : ℕ))) ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) :
        Finset V)) (_ : S.length + (2 : ℕ) = T.length) (_ : z1 ∈ TreeSequenceVertexSet S) (_ : z2
        ∈ TreeSequenceVertexSet S) (_ : z3 ∈ TreeSequenceVertexSet S) (_ :
    ∃ (S1 : TreeSequence G e0), TreeSequenceAdjoinEdge S g1 S1 ∧ TashkinovTree G e0 phiD S1),
        False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X U Z B hp g1 g2 hg2f0 g3 hg3f0 hg3g1 hg3g2 hproperD honeD
      hmissD hfixD phiD hg1data hg2data hg3data z1 z2 hz2Z z3 hz3Z w1 hw1X hw1g w2 hw2X hw2g w3
      hw3X hw3g he1 he2 he3 hproper hout_ne S hSvertices hSlength hz1S hz2S hz3S htreeS1
  rcases htreeS1 with ⟨S1, hS1, htreeS1⟩
  have adjoin_set (A B : TreeSequence G e0) (f : E) (x y : V)
      (hxy : G.ends f = s(x,y)) (hx : x ∈ TreeSequenceVertexSet A)
      (hy : y ∉ TreeSequenceVertexSet A) (hab : TreeSequenceAdjoinEdge A f B) :
      TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A) := by
    apply helper_adjoin_set_312 <;> assumption
  have hw1S : w1 ∉ TreeSequenceVertexSet S := by
    rw [hSvertices]; exact fun h => hw1X ((Finset.mem_sdiff.mp h).1)
  have hw2S : w2 ∉ TreeSequenceVertexSet S := by
    rw [hSvertices]; exact fun h => hw2X ((Finset.mem_sdiff.mp h).1)
  have hw3S : w3 ∉ TreeSequenceVertexSet S := by
    rw [hSvertices]; exact fun h => hw3X ((Finset.mem_sdiff.mp h).1)
  have hout_ne13 : w1 ≠ w3 := by
    intro h
    have hadj : AdjacentEdges G g1 g3 := ⟨w1, hw1g, by simpa [h] using hw3g⟩
    exact hproper (Ne.symm hg3g1) hadj
      (Finset.mem_filter.mp hg1data.1).2 (Finset.mem_filter.mp hg3data.1).2
  have hout_ne23 : w3 ≠ w2 := by
    intro h
    have hadj : AdjacentEdges G g3 g2 := ⟨w3, hw3g, by simpa [h] using hw2g⟩
    exact hproper hg3g2 hadj
      (Finset.mem_filter.mp hg3data.1).2 (Finset.mem_filter.mp hg2data.1).2
  have hS1set : TreeSequenceVertexSet S1 = insert w1 (TreeSequenceVertexSet S) :=
    adjoin_set S S1 g1 z1 w1 he1 hz1S hw1S hS1
  obtain ⟨S2, hS2⟩ := TreeSequenceBoundaryEdgeAppendExists S1 g2 (by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z2, by rw [hS1set]; exact Finset.mem_insert_of_mem hz2S,
      w2, by rw [hS1set]; simp [hw2S, hout_ne.symm], he2⟩)
  have hS2set : TreeSequenceVertexSet S2 = insert w2 (TreeSequenceVertexSet S1) :=
    adjoin_set S1 S2 g2 z2 w2 he2 (by
      rw [hS1set]
      exact Finset.mem_insert_of_mem hz2S) (by
      rw [hS1set]
      simp [hw2S, hout_ne.symm]) hS2
  have d_missing_S1 : d.1 ∈ TreeMissingColors phiD S1 := by
    rw [TreeMissingColors]
    refine Finset.mem_biUnion.mpr ⟨D.v0 d, ?_, ?_⟩
    · rw [hS1set]
      exact Finset.mem_insert_of_mem (by rw [hSvertices]; exact hp.1)
    · rw [hmissD]
      simp
  have htreeS2 := @helper_htreeS2_381 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@g2) (@hg2f0) (@hfixD) (@hg2data)
      (@z2) (@hz2Z) (@w2) (@he2) (@S1) (@htreeS1) (@S2) (@hS2) (@d_missing_S1)
  have hw1S2 : w1 ∈ TreeSequenceVertexSet S2 := by
    rw [hS2set]
    exact Finset.mem_insert_of_mem (by rw [hS1set]; simp [hw1S])
  have hw3S2 : w3 ∉ TreeSequenceVertexSet S2 := by
    apply helper_hw3S2_399 <;> assumption
  have hz3S2 : z3 ∈ TreeSequenceVertexSet S2 := by
    rw [hS2set]
    exact Finset.mem_insert_of_mem (by
      rw [hS1set]
      exact Finset.mem_insert_of_mem hz3S)
  have d_missing_S2 : d.1 ∈ TreeMissingColors phiD S2 := by
    rw [TreeMissingColors]
    refine Finset.mem_biUnion.mpr ⟨D.v0 d, ?_, ?_⟩
    · rw [hS2set, hS1set]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by rw [hSvertices]; exact hp.1))
    · rw [hmissD]
      simp
  obtain ⟨S3, hS3⟩ := TreeSequenceBoundaryEdgeAppendExists S2 g3 (by
    simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      using (show ∃ u ∈ TreeSequenceVertexSet S2, ∃ v ∉ TreeSequenceVertexSet S2,
        G.ends g3 = s(u, v) from ⟨z3, hz3S2, w3, hw3S2, he3⟩))
  have htreeS3 : TashkinovTree G e0 phiD S3 := by
    apply helper_htreeS3_424 <;> assumption
  have hle : (TreeSequenceVertexSet S3).card ≤ TashkinovOrder G := by
    apply helper_hle_439 <;> assumption
  have hcardS3 : (TreeSequenceVertexSet S3).card = S3.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective, S3.vertex_injective]
  have hcardS : (TreeSequenceVertexSet S).card = S.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective, S.vertex_injective]
  have hcardT : (TreeSequenceVertexSet T).card = T.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective, T.vertex_injective]
  rcases hS1 with ⟨hl1, hi1, he1'⟩
  rcases hS2 with ⟨hl2, hi2, he2'⟩
  rcases hS3 with ⟨hl3, hi3, he3'⟩
  rw [hcardS3] at hle
  have horder : TashkinovOrder G = S.length + 3 := by
    rw [(ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).1, hcardT]
    omega
  rw [horder] at hle
  omega

theorem ScheideReplacementBoundaryAtMostThree {V E : Type*}
    [vertexFinite : Fintype V] [edgeFinite : Fintype E] [vertexEquality : DecidableEq V]
        [edgeEquality : DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      let X := TreeSequenceVertexSet T
      let Z := X \ {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1}
      let B := @Finset.filter E (fun f => ∃ w, w ∉ X ∧ Incident G w f)
        (fun _ => Classical.propDecidable _) (BoundaryColorEdges G phi Z d.1)
      B.card ≤ 3 := by
  classical
  intro d
  dsimp
  let X := TreeSequenceVertexSet T
  let U := ({C.blockVertex (D.gammaIndex d) 0,
    C.blockVertex (D.gammaIndex d) 1} : Finset V)
  let Z := X \ U
  let B := @Finset.filter E (fun f => ∃ w, w ∉ X ∧ Incident G w f)
    (fun _ => Classical.propDecidable _) (BoundaryColorEdges G phi Z d.1)
  have hp := ScheideReplacementBoundaryParity G k e0 phi T C D d
  change D.v0 d ∈ Z ∧ _ ∧ _ ∧ D.f0 d ∈ B ∧ Odd B.card at hp
  by_contra hbad
  have hlarge : 5 ≤ B.card := by
    have hodd := hp.2.2.2.2
    rcases hodd with ⟨n, hn⟩
    have hgt : 3 < B.card := Nat.lt_of_not_ge hbad
    omega
  have hrest : 4 ≤ (B.erase (D.f0 d)).card := by
    rw [Finset.card_erase_of_mem hp.2.2.2.1]
    omega
  obtain ⟨g1, hg1⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hrest)
  have hg1f0 : g1 ≠ D.f0 d := (Finset.mem_erase.mp hg1).1
  have hg1B : g1 ∈ B := by
    exact Finset.mem_of_mem_erase hg1
  have hrest1 : 3 ≤ ((B.erase (D.f0 d)).erase g1).card := by
    rw [Finset.card_erase_of_mem hg1]
    omega
  obtain ⟨g2, hg2⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hrest1)
  have hg2B : g2 ∈ B := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg2)
  have hg2f0 : g2 ≠ D.f0 d := by
    intro h
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hg2)).1 h
  have hg2g1 : g2 ≠ g1 := (Finset.mem_erase.mp hg2).1
  have hrest2 : 2 ≤ (((B.erase (D.f0 d)).erase g1).erase g2).card := by
    rw [Finset.card_erase_of_mem hg2]
    omega
  obtain ⟨g3, hg3⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hrest2)
  have hg3B : g3 ∈ B := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hg3))
  have hg3f0 : g3 ≠ D.f0 d := by
    intro h
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase hg3))).1 h
  have hg3g1 : g3 ≠ g1 := by
    intro h
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hg3)).1 h
  have hg3g2 : g3 ≠ g2 := (Finset.mem_erase.mp hg3).1
  have hswitch := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  rcases hswitch with ⟨hproperD, honeD, hf0D, hmissD, hfixD, htreeD, hcompD⟩
  let phiD := TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
    (Sum.inl (D.v0 d))
  have hg1data : g1 ∈ BoundaryColorEdges G phi Z d.1 ∧ ∃ w, w ∉ X ∧ Incident G w g1 := by simpa
      [B] using hg1B
  have hg2data : g2 ∈ BoundaryColorEdges G phi Z d.1 ∧ ∃ w, w ∉ X ∧ Incident G w g2 := by simpa
      [B] using hg2B
  have hg3data : g3 ∈ BoundaryColorEdges G phi Z d.1 ∧ ∃ w, w ∉ X ∧ Incident G w g3 := by simpa
      [B] using hg3B
  have hB1 : g1 ∈ BoundaryEdges G Z := (Finset.mem_filter.mp hg1data.1).1
  have hB2 : g2 ∈ BoundaryEdges G Z := (Finset.mem_filter.mp hg2data.1).1
  have hB3 : g3 ∈ BoundaryEdges G Z := (Finset.mem_filter.mp hg3data.1).1
  obtain ⟨z1, hz1Z, wz1, hwz1Z, hez1⟩ := by simpa [BoundaryEdges] using hB1
  obtain ⟨z2, hz2Z, wz2, hwz2Z, hez2⟩ := by simpa [BoundaryEdges] using hB2
  obtain ⟨z3, hz3Z, wz3, hwz3Z, hez3⟩ := by simpa [BoundaryEdges] using hB3
  obtain ⟨w1, hw1X, hw1g⟩ := hg1data.2
  obtain ⟨w2, hw2X, hw2g⟩ := hg2data.2
  obtain ⟨w3, hw3X, hw3g⟩ := hg3data.2
  have pair_end : ∀ {a b : V} {f : E}, a ∈ G.ends f → b ∈ G.ends f → a ≠ b →
      G.ends f = s(a,b) := by
    intro a b f ha hb hab
    exact (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩
  have he1 : G.ends g1 = s(z1,w1) := by
    apply pair_end
    · rw [hez1]; simp
    · exact hw1g
    · intro h; exact hw1X (h ▸ (Finset.mem_sdiff.mp hz1Z).1)
  have he2 : G.ends g2 = s(z2,w2) := by
    apply pair_end
    · rw [hez2]; simp
    · exact hw2g
    · intro h; exact hw2X (h ▸ (Finset.mem_sdiff.mp hz2Z).1)
  have he3 : G.ends g3 = s(z3,w3) := by
    apply pair_end
    · rw [hez3]; simp
    · exact hw3g
    · intro h; exact hw3X (h ▸ (Finset.mem_sdiff.mp hz3Z).1)
  have hproper : IsProperEdgeColoring G phi := C.globally_maximum.1.2.2.2.1
  have hout_ne := @helper_hout_ne_132 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@g1) (@g2) (@hg2g1) (@hg1data)
      (@hg2data) (@w1) (@hw1g) (@w2) (@hw2g) (@hproper)
  have hdel := ScheideSelectedBlockDeletion G k e0 phi T C (D.gammaIndex d)
  rcases hdel with ⟨S, hSvertices, hSlength, hvertexReindex, hedgeReindex,
    hbaseVertices, hbaseEdges, hblockEntries, hedgeCases, hedgeOld,
    hnotIncident⟩
  have htreeOld : TashkinovTree G e0 phi T := C.globally_maximum.2.1
  have hunused := ScheideGlobalMaximumUnused G k e0 phi T C.globally_maximum
  have hdeltaNotMissing : ∀ v, v ∈ X → d.1 ∉ MissingColors G phi v := by
    apply helper_hdeltaNotMissing_146 <;> assumption
  have tree_edge_incident : ∀ q : Fin T.length, TreeIncidentEdge T (T.edge q) := by
    apply SharedFacts.ScheideDefectiveNoCross.tree_edge_incident
  have edge_color_D (q : Fin T.length) (c : Fin k)
      (hc : phi (T.edge q) = some c) : phiD (T.edge q) = some c := by
    apply helper_edge_color_D_163 <;> assumption
  have missing_unaffected (v : V) (hv : v ∈ X) (c : Fin k)
      (hc : c ≠ C.gamma (D.gammaIndex d)) (hd : c ≠ d.1) :
      (c ∈ MissingColors G phiD v ↔ c ∈ MissingColors G phi v) := by
    apply helper_missing_unaffected_183 <;> assumption
  have htreeS : TashkinovTree G e0 phiD S := by
    apply helper_htreeS_191 <;> assumption
  have hz1S : z1 ∈ TreeSequenceVertexSet S := by
    rw [hSvertices]
    exact hz1Z
  have hz2S : z2 ∈ TreeSequenceVertexSet S := by rw [hSvertices]; exact hz2Z
  have hz3S : z3 ∈ TreeSequenceVertexSet S := by rw [hSvertices]; exact hz3Z
  have htreeS1 : ∃ S1, TreeSequenceAdjoinEdge S g1 S1 ∧
      TashkinovTree G e0 phiD S1 := by
    have hz := (Finset.mem_sdiff.mp hz1Z).1
    have hw : w1 ∉ TreeSequenceVertexSet S := by
      rw [hSvertices]
      intro hw
      exact hw1X (Finset.mem_sdiff.mp hw).1
    have d_missing_S : d.1 ∈ TreeMissingColors phiD S := by
      rw [TreeMissingColors]
      refine Finset.mem_biUnion.mpr ⟨D.v0 d, ?_, ?_⟩
      · rw [hSvertices]
        exact hp.1
      · rw [hmissD]
        simp
    obtain ⟨S1, hS1⟩ := TreeSequenceBoundaryEdgeAppendExists S g1 (by
      simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        using (show ∃ u ∈ TreeSequenceVertexSet S, ∃ v ∉ TreeSequenceVertexSet S,
          G.ends g1 = s(u, v) from ⟨z1, hz1S, w1, hw, he1⟩))
    refine ⟨S1, hS1, ?_⟩
    apply TashkinovAugmentationSequencePreservesTashkinovTree G e0 phiD S S1 htreeS
    rcases hS1 with ⟨hlen, hinit, hlast⟩
    exact Relation.ReflTransGen.single ⟨hlen, hinit, d.1,
      (congrArg phiD hlast).trans (by
        have hf := hfixD g1
          (show ∃ v ∈ TreeSequenceVertexSet T, Incident G v g1 from
            ⟨z1, (Finset.mem_sdiff.mp hz1Z).1, by
              change z1 ∈ G.ends g1
              rw [he1]
              simp⟩) hg1f0
        calc
          phiD g1 = phi g1 := by simpa [phiD] using hf
          _ = some d.1 := (Finset.mem_filter.mp hg1data.1).2), d_missing_S⟩
  exact @helper_continuation_668 (@V) (@E) vertexFinite edgeFinite vertexEquality edgeEquality
      (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (by
    simpa only [X, U, Z, B] using hp) (@g1) (@g2) (@hg2f0) (@g3) (@hg3f0) (@hg3g1) (@hg3g2)
        (@hproperD) (@honeD) (@hmissD) (@hfixD) (@hg1data) (@hg2data) (@hg3data) (@z1) (@z2)
        (@hz2Z) (@z3) (@hz3Z) (@w1) (@hw1X) (@hw1g) (@w2) (@hw2X) (@hw2g) (@w3) (@hw3X) (@hw3g)
        (@he1) (@he2) (@he3) (@hproper) (@hout_ne) (@S) (@hSvertices) (@hSlength) (@hz1S) (@hz2S)
        (@hz3S) (@htreeS1)
end GoldbergSeymour

end
