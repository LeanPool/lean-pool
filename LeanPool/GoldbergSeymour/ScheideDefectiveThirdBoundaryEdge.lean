/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.ScheideDefectiveThirdBoundaryEdge

public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.ScheideDefectiveDeletedTreePair
public import LeanPool.GoldbergSeymour.ScheideDefectiveNoCross
public import LeanPool.GoldbergSeymour.ScheideDefectiveReturnData
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Scheide Defective Third Boundary Edge

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private abbrev helperContinuation1024Conditions.{u_1, u_2} : Prop :=
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
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let K : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let KJ : Set (V ⊕ E) := TwoColorComponent G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k) (Sum.inl
        R.v1);
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks; TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤
        (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T) → (
    ∀ (r : Fin C.s) (b : Fin (2 : ℕ)), C.blockVertex r b ∈ X) → (
    ∀ (a : Fin C.p), C.y a ∈ Z) → C.blockVertex j (0 : Fin (2 : ℕ)) ≠ C.blockVertex j (1 : Fin (2
        : ℕ)) → blocks ⊆ X → R.v1 ∈ Z →
    ∀ (f2 : E), f2 ≠ D.f0 d → f2 ≠ R.f1 → phi f2 = some (↑d : Fin k) →
    ∀ z2 ∈ Z,
    ∀ u2 ∉ Z, G.ends f2 = s(z2, u2) → z2 ∈ X → z2 ≠ D.v0 d → z2 ≠ R.v1 → u2 ≠ D.u0 d → u2 ≠ R.u1 →
        (
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ↔ v = D.v0 d) → IsProperEdgeColoring G (OutsideTreeColorSwap T phi (C.gamma
        (D.gammaIndex d)) (C.gamma R.blockIndex)) → StableColoring T ∅ phi (OutsideTreeColorSwap T
        phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) → (
    ∀ (f : E), TreeIncidentEdge T f → OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d))
        (C.gamma R.blockIndex) f = phi f) → (
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G (OutsideTreeColorSwap T phi
        (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k)
        (Sum.inl R.v1) ↔ v = R.v1) → IsProperEdgeColoring G (TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma
        R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) → IsOneEdgeUncolored (TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma
        R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) e0 → (↑d : Fin k) ∈ MissingColors G
        (TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) R.v1 →
        TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1) (D.f0 d) = some (↑d :
        Fin k) → phi1 f2 = some (↑d : Fin k) → psi1 f2 = some (↑d : Fin k) → (
    ∀ {v : V} {e : E}, Sum.inr e ∈ K → Incident G v e → phi1 e = some gamma ∨ phi1 e = some (↑d :
        Fin k) → Sum.inl v ∈ K) → (
    ∀ {v : V} {e : E}, Sum.inr e ∈ KJ → Incident G v e → psi1 e = some gammaJ ∨ psi1 e = some (↑d
        : Fin k) → Sum.inl v ∈ KJ) →
    ∃ (f2 : E) (z2 : V) (u2 : V), phi f2 = some (↑d : Fin k) ∧ G.ends f2 = s(z2, u2) ∧ z2 ∈
        TreeSequenceVertexSet T \ ({C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪ {C.blockVertex R.blockIndex (0 : Fin
        (2 : ℕ)), C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))}) ∧ u2 ∉ TreeSequenceVertexSet T ∧
        f2 ≠ D.f0 d ∧ f2 ≠ R.f1 ∧ z2 ≠ D.v0 d ∧ z2 ≠ R.v1 ∧ TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f2 = some (↑d : Fin k) ∧ TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma
        R.blockIndex) (↑d : Fin k) (Sum.inl R.v1) f2 = some (↑d : Fin k) ∧ u2 ≠ D.u0 d ∧ u2 ≠ R.u1

private theorem helper_adjoin_vertex_set_647.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] (G : LooplessMultigraph V E) (e0 : E) (A0 A1 :
        TreeSequence G e0) (f : E) (x y : V), G.ends f = s(x, y) → y ∉ TreeSequenceVertexSet A0 →
        TreeSequenceAdjoinEdge A0 f A1 → TreeSequenceVertexSet A1 = insert y
        (TreeSequenceVertexSet A0) := by
  classical
  intro V E _ G e0 A0 A1 f x y hxy hyA hAA
  rcases hAA with ⟨hlen, hinit, hlast⟩
  rcases hinit with ⟨hle, hvertices, hedges⟩
  have holdSubset : TreeSequenceVertexSet A0 ⊆ TreeSequenceVertexSet A1 := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨q, hq⟩ := hv
    refine ⟨Fin.castLE (Nat.succ_le_succ hle) q, ?_⟩
    rw [hvertices]
    exact hq
  have hyB : y ∈ TreeSequenceVertexSet A1 := by
    let q : Fin A1.length := Fin.cast hlen.symm (Fin.last A0.length)
    obtain ⟨a, ha⟩ := A1.attaches q
    have hyEnds : y ∈ G.ends (A1.edge q) := by
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
  have hinsert : insert y (TreeSequenceVertexSet A0) ⊆
      TreeSequenceVertexSet A1 := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact hyB
    · exact holdSubset hv
  have hAcard : (TreeSequenceVertexSet A0).card = A0.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      A0.vertex_injective]
  have hBcard : (TreeSequenceVertexSet A1).card = A1.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      A1.vertex_injective]
  have hcard : (TreeSequenceVertexSet A1).card ≤
      (insert y (TreeSequenceVertexSet A0)).card := by
    rw [hBcard, Finset.card_insert_of_notMem hyA, hAcard, hlen]
  exact (Finset.eq_of_subset_of_card_le hinsert hcard).symm

private theorem helper_hfinalVertices_391.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks;
    ∀ (f2 : E) (z2 u2 : V), u2 ∉ Z → G.ends f2 = s(z2, u2) → u2 ≠ D.u0 d → u2 ≠ R.u1 → u2 ∉ Ui →
        u2 ∈ Uj →
    ∀ (SgammaJ : TreeSequence G e0), TreeSequenceVertexSet SgammaJ = TreeSequenceVertexSet T \
        {C.blockVertex R.blockIndex (0 : Fin (2 : ℕ)), C.blockVertex R.blockIndex (1 : Fin (2 :
        ℕ))} ∪ {D.u0 d} → u2 ∉ TreeSequenceVertexSet SgammaJ →
    ∀ (Splus : TreeSequence G e0), TreeSequenceVertexSet Splus = insert u2 (TreeSequenceVertexSet
        SgammaJ) →
    ∀ (g : E),
    ∀ w2 ∈ Uj, w2 ≠ u2 → Uj = { u2, w2 } → G.ends g = s(u2, w2) → u2 ∈ X → w2 ∈ X → w2 ≠ D.u0 d →
        w2 ∉ TreeSequenceVertexSet SgammaJ → w2 ∉ TreeSequenceVertexSet Splus →
    ∀ (Splusplus : TreeSequence G e0), TreeSequenceVertexSet Splusplus = insert w2
        (TreeSequenceVertexSet Splus) → TreeSequenceVertexSet Splusplus = insert (D.u0 d) X := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j Ui Uj blocks Z f2 z2 u2 hu2Z hf2ends hu2u0 hu2u1
      hu2Ui hu2Uj SgammaJ hSgammaJVertices hu2NotS Splus hSplusVertices g w2 hw2Uj hw2ne hUjPair
      hgends' hu2X hw2X hw2u0 hw2NotS hw2NotSplus Splusplus hSplusplusVertices
  rw [hSplusplusVertices, hSplusVertices, hSgammaJVertices]
  have hUjPair' :
      ({C.blockVertex R.blockIndex 0,
          C.blockVertex R.blockIndex 1} : Finset V) = {u2, w2} := by
    simpa [Uj, j] using hUjPair
  rw [hUjPair']
  ext v
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | (⟨hvX, hneU⟩ | rfl))
    · exact Or.inr hw2X
    · exact Or.inr hu2X
    · exact Or.inr hvX
    · exact Or.inl rfl
  · rintro (rfl | hvX)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · by_cases hvu : v = u2
      · exact Or.inr (Or.inl hvu)
      · by_cases hvw : v = w2
        · exact Or.inl hvw
        · exact Or.inr (Or.inr (Or.inl ⟨hvX, by simp [hvu, hvw]⟩))

private theorem helper_continuation_430.{u_1, u_2} :
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
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks; TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤
        (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T) → blocks ⊆ X →
    ∀ (f2 : E) (z2 u2 : V), u2 ∉ Z → G.ends f2 = s(z2, u2) → u2 ≠ D.u0 d → u2 ≠ R.u1 →
        IsProperEdgeColoring G (TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma
        (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl
        R.v1)) → IsOneEdgeUncolored (TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma
        (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl
        R.v1)) e0 → u2 ∉ Ui → (
    ∀ (rho : PartialEdgeColoring E k) (S U : TreeSequence G e0) (f : E), TreeSequenceAdjoinEdge S
        f U → TashkinovTree G e0 rho S →
    ∀ (c : Fin k), rho f = some c →
    ∀ v ∈ TreeSequenceVertexSet S, c ∈ MissingColors G rho v → TashkinovTree G e0 rho U) → (
    ∀ (A0 A1 : TreeSequence G e0) (f : E) (x y : V), G.ends f = s(x, y) → x ∈
        TreeSequenceVertexSet A0 → y ∉ TreeSequenceVertexSet A0 → TreeSequenceAdjoinEdge A0 f A1 →
        TreeSequenceVertexSet A1 = insert y (TreeSequenceVertexSet A0)) → u2 ∈ Uj →
    ∀ (SgammaJ : TreeSequence G e0), TreeSequenceVertexSet SgammaJ = TreeSequenceVertexSet T \
        {C.blockVertex R.blockIndex (0 : Fin (2 : ℕ)), C.blockVertex R.blockIndex (1 : Fin (2 :
        ℕ))} ∪ {D.u0 d} → u2 ∉ TreeSequenceVertexSet SgammaJ →
    ∀ (Splus : TreeSequence G e0), TashkinovTree G e0 psi2 Splus → TreeSequenceVertexSet Splus =
        insert u2 (TreeSequenceVertexSet SgammaJ) →
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    ∀ (g : E), psi2 g = some D.alpha0 → D.alpha0 ∈ MissingColors G psi2 y0 → y0 ∈
        TreeSequenceVertexSet Splus →
    ∀ w2 ∈ Uj, w2 ≠ u2 → Uj = { u2, w2 } → G.ends g = s(u2, w2) → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ psi1 psi2 Ui Uj blocks Z horder
      hblocksSub f2 z2 u2 hu2Z hf2ends hu2u0 hu2u1 hproperJ2 honeJ2 hu2Ui tashkinov_adjoin
      adjoin_vertex_set hu2Uj SgammaJ hSgammaJVertices hu2NotS Splus hSplusTash hSplusVertices y0
      g hpsi2g hy0MissingPsi2 hy0Splus w2 hw2Uj hw2ne hUjPair hgends'
  have hu2X : u2 ∈ X := hblocksSub
    (Finset.mem_union.mpr (Or.inr hu2Uj))
  have hw2X : w2 ∈ X := hblocksSub
    (Finset.mem_union.mpr (Or.inr hw2Uj))
  have hw2u0 : w2 ≠ D.u0 d := by
    intro h
    exact D.u0_outside d (h ▸ hw2X)
  have hw2NotS : w2 ∉ TreeSequenceVertexSet SgammaJ := by
    rw [hSgammaJVertices]
    intro hw
    rcases Finset.mem_union.mp hw with hwOld | hw0
    · exact (Finset.mem_sdiff.mp hwOld).2
        (by simpa [Uj, j] using hw2Uj)
    · exact hw2u0 (by simpa using hw0)
  have hw2NotSplus : w2 ∉ TreeSequenceVertexSet Splus := by
    rw [hSplusVertices]
    simp [hw2ne, hw2NotS]
  have hgBoundary : g ∈ BoundaryEdges G (TreeSequenceVertexSet Splus) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u2, by simp [hSplusVertices], w2, hw2NotSplus, hgends'⟩
  obtain ⟨Splusplus, hSplusplus⟩ :=
    TreeSequenceBoundaryEdgeAppendExists Splus g hgBoundary
  have hSplusplusTash : TashkinovTree G e0 psi2 Splusplus :=
    tashkinov_adjoin psi2 Splus Splusplus g hSplusplus hSplusTash
      D.alpha0 hpsi2g y0 hy0Splus hy0MissingPsi2
  have hSplusplusVertices : TreeSequenceVertexSet Splusplus =
      insert w2 (TreeSequenceVertexSet Splus) :=
    adjoin_vertex_set Splus Splusplus g u2 w2 hgends'
      (by simp [hSplusVertices]) hw2NotSplus hSplusplus
  have hfinalVertices := @helper_hfinalVertices_391 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R f2 z2 u2 hu2Z hf2ends hu2u0 hu2u1 hu2Ui hu2Uj SgammaJ
      hSgammaJVertices hu2NotS Splus hSplusVertices g w2 hw2Uj hw2ne hUjPair hgends' hu2X hw2X hw2u0
      hw2NotS hw2NotSplus Splusplus hSplusplusVertices
  have hK2 : KTriple G k e0 psi2 :=
    ⟨C.globally_maximum.1.1, C.globally_maximum.1.2.1,
      C.globally_maximum.1.2.2.1, hproperJ2, honeJ2⟩
  have hle := treeCard_le_tashkinovOrder G k e0 psi2 Splusplus hK2 hSplusplusTash
  rw [hfinalVertices, Finset.card_insert_of_notMem (D.u0_outside d),
    horder.1] at hle
  exact (Nat.not_succ_le_self X.card) hle

private theorem helper_hu2Uj_695.{u_1, u_2} :
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
    let _ : Set (V ⊕ E) := TwoColorComponent G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    let psi2 : PartialEdgeColoring E k := TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k)
        (Sum.inl R.v1);
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks; TashkinovOrder G = (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤
        (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T) → (
    ∀ (r : Fin C.s) (b : Fin (2 : ℕ)), C.blockVertex r b ∈ X) → (
    ∀ (a : Fin C.p), C.y a ∈ Z) → C.blockVertex j (0 : Fin (2 : ℕ)) ≠ C.blockVertex j (1 : Fin (2
        : ℕ)) → blocks ⊆ X → R.v1 ∈ Z →
    ∀ (f2 : E),
    ∀ z2 ∈ Z,
    ∀ u2 ∉ Z, G.ends f2 = s(z2, u2) → z2 ∈ X → u2 ≠ D.u0 d → u2 ≠ R.u1 → IsProperEdgeColoring G
        (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) →
        StableColoring T ∅ phi (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) → (
    ∀ (f : E), TreeIncidentEdge T f → OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d))
        (C.gamma R.blockIndex) f = phi f) → IsProperEdgeColoring G (TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma
        R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) → IsOneEdgeUncolored (TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma
        R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) e0 → (↑d : Fin k) ∈ MissingColors G
        (TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1)) R.v1 →
        TwoColorComponentSwap G (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma
        R.blockIndex)) (C.gamma R.blockIndex) (↑d : Fin k) (Sum.inl R.v1) (D.f0 d) = some (↑d :
        Fin k) → psi2 f2 = some (↑d : Fin k) → u2 ∉ Ui → (
    ∀ (rho : PartialEdgeColoring E k) (S U : TreeSequence G e0) (f : E), TreeSequenceAdjoinEdge S
        f U → TashkinovTree G e0 rho S →
    ∀ (c : Fin k), rho f = some c →
    ∀ v ∈ TreeSequenceVertexSet S, c ∈ MissingColors G rho v → TashkinovTree G e0 rho U) → (
    ∀ (A0 A1 : TreeSequence G e0) (f : E) (x y : V), G.ends f = s(x, y) → x ∈
        TreeSequenceVertexSet A0 → y ∉ TreeSequenceVertexSet A0 → TreeSequenceAdjoinEdge A0 f A1 →
        TreeSequenceVertexSet A1 = insert y (TreeSequenceVertexSet A0)) → u2 ∉ Uj := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ psi1 KJ psi2 Ui Uj blocks Z horder
      block_mem_X base_mem_Z hj01 hblocksSub hv1Z f2 z2 hz2Z u2 hu2Z hf2ends hz2X hu2u0 hu2u1
      hproperJ1 hstableJ1 hfixedJ1 hproperJ2 honeJ2 hdeltaMissingJ2 hf0colorJ2 hpsi2f2 hu2Ui
      tashkinov_adjoin adjoin_vertex_set hu2Uj
  have hpairs := ScheideDefectiveDeletedTreePair G k e0 phi T C D d R
  dsimp only at hpairs
  rcases hpairs with
    ⟨Sgamma, SgammaJ, hSgammaTash, hSgammaVertices,
      hSgammaJTash, hSgammaJVertices, hf1color2, hf0colorJ2⟩
  have hz2NotUj : z2 ∉ Uj := by
    intro hz2Uj
    exact (Finset.mem_sdiff.mp hz2Z).2
      (Finset.mem_union.mpr (Or.inr hz2Uj))
  have hz2S : z2 ∈ TreeSequenceVertexSet SgammaJ := by
    rw [hSgammaJVertices]
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mpr ⟨hz2X, by simpa [Uj, j] using hz2NotUj⟩))
  have hu2NotS : u2 ∉ TreeSequenceVertexSet SgammaJ := by
    rw [hSgammaJVertices]
    intro hu
    rcases Finset.mem_union.mp hu with huOld | hu0
    · exact (Finset.mem_sdiff.mp huOld).2
        (by simpa [Uj, j] using hu2Uj)
    · exact hu2u0 (by simpa using hu0)
  have hf2BoundaryS : f2 ∈ BoundaryEdges G
      (TreeSequenceVertexSet SgammaJ) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z2, hz2S, u2, hu2NotS, hf2ends⟩
  obtain ⟨Splus, hSplus⟩ :=
    TreeSequenceBoundaryEdgeAppendExists SgammaJ f2 hf2BoundaryS
  have hSplusTash : TashkinovTree G e0 psi2 Splus :=
    tashkinov_adjoin psi2 SgammaJ Splus f2 hSplus hSgammaJTash d.1
      hpsi2f2 R.v1 (by
        rw [hSgammaJVertices]
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv1Z).1,
            by
              intro hv1Uj
              exact (Finset.mem_sdiff.mp hv1Z).2
                (Finset.mem_union.mpr (Or.inr (by simpa [Uj, j] using hv1Uj)))⟩)))
      hdeltaMissingJ2
  have hSplusVertices : TreeSequenceVertexSet Splus =
      insert u2 (TreeSequenceVertexSet SgammaJ) :=
    adjoin_vertex_set SgammaJ Splus f2 z2 u2 hf2ends hz2S hu2NotS hSplus
  let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0Z : y0 ∈ Z := by
    exact base_mem_Z ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0X : y0 ∈ X := (Finset.mem_sdiff.mp hy0Z).1
  have hy0NotUj : y0 ∉ Uj := by
    intro hy0Uj
    exact (Finset.mem_sdiff.mp hy0Z).2
      (Finset.mem_union.mpr (Or.inr hy0Uj))
  obtain ⟨g, hgcolor, hgends⟩ :=
    ScheideStructuralInternalPair G k e0 phi T C j D.alpha0
      (by simpa [gammaJ, j] using R.alpha0_ne_gammaJ)
      ⟨y0, by
        apply Finset.mem_sdiff.mpr
        exact ⟨hy0X, by simpa [Uj, j] using hy0NotUj⟩,
        by simpa [y0] using D.alpha0_missing_at_y0⟩
  have hpsi1g : psi1 g = some D.alpha0 := by
    apply (hfixedJ1 g ?_).trans hgcolor
    exact ⟨C.blockVertex j 0, block_mem_X j 0,
      by simp [Incident, hgends]⟩
  have hpsi2g : psi2 g = some D.alpha0 := by
    by_cases hgK : Sum.inr g ∈ KJ
    · have halphaGamma : D.alpha0 ≠ gammaJ := by
        simpa [gammaJ, j] using R.alpha0_ne_gammaJ
      simp [psi2, TwoColorComponentSwap, KJ, hgK, hpsi1g,
        halphaGamma, R.alpha0_ne_delta]
    · simp [psi2, TwoColorComponentSwap, KJ, hgK, hpsi1g]
  have hbehaviorJ := TwoColorComponentSwapMissingBehavior G psi1 gammaJ d.1
    (by simpa [gammaJ, j] using R.gammaJ_ne_delta) hproperJ1
    (Sum.inl R.v1)
  have hy0MissingPsi1 : D.alpha0 ∈ MissingColors G psi1 y0 := by
    rw [hstableJ1.2 y0 hy0X]
    simpa [y0] using D.alpha0_missing_at_y0
  have hy0MissingPsi2 : D.alpha0 ∈ MissingColors G psi2 y0 := by
    exact (hbehaviorJ.2.2.2 y0 D.alpha0
      (by simpa [gammaJ, j] using R.alpha0_ne_gammaJ)
      R.alpha0_ne_delta).mpr hy0MissingPsi1
  have hy0Splus : y0 ∈ TreeSequenceVertexSet Splus := by
    rw [hSplusVertices, hSgammaJVertices]
    exact Finset.mem_insert_of_mem (Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mpr
        ⟨hy0X, by simpa [Uj, j] using hy0NotUj⟩)))
  obtain ⟨w2, hw2Uj, hw2ne, hUjPair, hgends'⟩ :
      ∃ w2 : V, w2 ∈ Uj ∧ w2 ≠ u2 ∧ Uj = {u2, w2} ∧
        G.ends g = s(u2, w2) := by
    simp only [Uj, Finset.mem_insert, Finset.mem_singleton] at hu2Uj
    rcases hu2Uj with hu2j0 | hu2j1
    · refine ⟨C.blockVertex j 1, by simp [Uj], ?_, ?_, ?_⟩
      · intro h
        exact hj01 (hu2j0.symm.trans h.symm)
      · simp [Uj, hu2j0]
      · simpa [hu2j0] using hgends
    · refine ⟨C.blockVertex j 0, by simp [Uj], ?_, ?_, ?_⟩
      · intro h
        exact hj01 (h.trans hu2j1)
      · simp [Uj, hu2j1, Finset.pair_comm]
      · rw [hu2j1]
        exact hgends.trans Sym2.eq_swap
  exact @helper_continuation_430 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R horder hblocksSub f2 z2 u2 hu2Z hf2ends hu2u0 hu2u1 hproperJ2 honeJ2 hu2Ui
      tashkinov_adjoin adjoin_vertex_set hu2Uj SgammaJ hSgammaJVertices hu2NotS Splus hSplusTash
      hSplusVertices g hpsi2g hy0MissingPsi2 hy0Splus w2 hw2Uj hw2ne hUjPair hgends'
private theorem helper_block_vertex_injective_478.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T),
    T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s →
    Function.Injective fun (q : Fin C.s × Fin (2 : ℕ)) ↦ C.blockVertex q.1 q.2 := by
  classical
  intro V E _ _ _ G k e0 phi T C hlength a b hab
  let qa : Fin (T.length + 1) :=
    ⟨C.p + 2 * a.1.val + a.2.val, by
      have ha1 := a.1.isLt
      have ha2 := a.2.isLt
      omega⟩
  let qb : Fin (T.length + 1) :=
    ⟨C.p + 2 * b.1.val + b.2.val, by
      have hb1 := b.1.isLt
      have hb2 := b.2.isLt
      omega⟩
  have hv : T.vertex qa = T.vertex qb := by
    rw [show T.vertex qa = C.blockVertex a.1 a.2 by
      simpa [qa] using C.block_vertex_position a.1 a.2]
    rw [show T.vertex qb = C.blockVertex b.1 b.2 by
      simpa [qb] using C.block_vertex_position b.1 b.2]
    exact hab
  have hq := congrArg Fin.val (T.vertex_injective hv)
  apply Prod.ext
  · apply Fin.ext
    dsimp [qa, qb] at hq
    have ha2 := a.2.isLt
    have hb2 := b.2.isLt
    omega
  · apply Fin.ext
    dsimp [qa, qb] at hq
    have ha2 := a.2.isLt
    have hb2 := b.2.isLt
    omega

private theorem helper_base_ne_block_526.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T),
    T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s →
    ∀ (a : Fin C.p) (r : Fin C.s) (b : Fin (2 : ℕ)),
    C.y a ≠ C.blockVertex r b := by
  classical
  intro V E _ _ _ G k e0 phi T C hlength a r b h
  let qa : Fin (T.length + 1) := ⟨a.val, by
    have ha := a.isLt
    have hr := r.isLt
    have hb := b.isLt
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

private theorem helper_hgood_union_640.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks;
    let edges : Finset E := {e : E | phi e = some (↑d : Fin k)};
    let good : Finset E := {e ∈ edges |
    ∀ (v : V), Incident G v e → v ∈ Z}; (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) → (
    ∀ ⦃e : E⦄, e ∈ good →
    ∀ ⦃f : E⦄, f ∈ good → e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset) →
        (good.biUnion fun (e : E) ↦ (G.ends e).toFinset).card = (2 : ℕ) * good.card := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j Ui Uj blocks Z edges good hendcard hgood_disjoint
  as_aux_lemma =>
  have aux : ∀ s : Finset E, s ⊆ good →
      (s.biUnion fun e => (G.ends e).toFinset).card = 2 * s.card := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s hes ih =>
      rw [Finset.biUnion_insert]
      have hd : Disjoint (G.ends e).toFinset
          (s.biUnion fun f => (G.ends f).toFinset) := by
        rw [Finset.disjoint_left]
        intro v hev hvs
        obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvs
        have hh := hgood_disjoint (hs (Finset.mem_insert_self e s))
          (hs (Finset.mem_insert_of_mem hf)) (by
            intro heq
            exact hes (by simpa [heq] using hf))
        exact (Finset.disjoint_left.mp hh) hev hvf
      rw [Finset.card_union_of_disjoint hd, hendcard]
      rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
      rw [Finset.card_insert_of_notMem hes]
      omega
  exact aux good (by intro e he; exact he)

private theorem helper_hgood_cover_665.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks;
    let B : Finset E := BoundaryColorEdges G phi Z (↑d : Fin k);
    let edges : Finset E := {e : E | phi e = some (↑d : Fin k)};
    let good : Finset E := {e ∈ edges |
    ∀ (v : V), Incident G v e → v ∈ Z}; (
    ∀ v ∈ Z, (↑d : Fin k) ∈ PresentColors G phi v) → (
    ∀ (e : E), e ∈ edges ↔ phi e = some (↑d : Fin k)) → (
    ∀ (e : E), e ∈ good ↔ e ∈ edges ∧
    ∀ (v : V), Incident G v e → v ∈ Z) →
    ∀ v ∈ Z, (v ∈ good.biUnion fun (e : E) ↦ (G.ends e).toFinset) ∨ v ∈ B.biUnion fun (e : E) ↦
        {v ∈ Z | Incident G v e} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j Ui Uj blocks Z B edges good hpresent hedge_mem hgood
  as_aux_lemma =>
  intro v hv
  obtain ⟨e, he, hve⟩ := by
    simpa [PresentColors] using hpresent v hv
  by_cases hall : ∀ w, Incident G w e → w ∈ Z
  · left
    exact Finset.mem_biUnion.mpr
      ⟨e, (hgood e).mpr ⟨(hedge_mem e).mpr hve, hall⟩,
        Sym2.mem_toFinset.mpr he⟩
  · right
    push Not at hall
    obtain ⟨w, hw, hwo⟩ := hall
    obtain ⟨z, hze⟩ := Sym2.mem_iff_exists.mp hw
    have heq : G.ends e = s(w, z) := hze
    have hzZ : z ∈ Z := by
      have hvEnds : v = w ∨ v = z := by
        have : v ∈ s(w, z) := by rw [← heq]; exact he
        simpa using this
      rcases hvEnds with rfl | rfl
      · exact False.elim (hwo hv)
      · exact hv
    have hbound : e ∈ BoundaryEdges G Z := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨z, hzZ, w, hwo, heq.trans Sym2.eq_swap⟩
    exact Finset.mem_biUnion.mpr ⟨e,
      (Finset.mem_filter.mpr ⟨hbound, hve⟩),
      Finset.mem_filter.mpr ⟨hv, he⟩⟩

private theorem helper_hb_union_724.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks;
    let B : Finset E := BoundaryColorEdges G phi Z (↑d : Fin k); (
    ∀ e ∈ B, {v ∈ Z | Incident G v e}.card = (1 : ℕ)) → (
    ∀ ⦃e : E⦄, e ∈ B →
    ∀ ⦃f : E⦄, f ∈ B → e ≠ f → Disjoint ({v ∈ Z | Incident G v e}) ({v ∈ Z | Incident G v f})) →
        (B.biUnion fun (e : E) ↦ {v ∈ Z | Incident G v e}).card = B.card := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j Ui Uj blocks Z B hb_fiber hb_disjoint
  as_aux_lemma =>
  have aux :
    ∀ s : Finset E, s ⊆ B → (s.biUnion fun e => Z.filter (fun v => Incident G v e)).card = s.card
  := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s hes ih =>
      rw [Finset.biUnion_insert]
      have hd : Disjoint (Z.filter (fun v => Incident G v e))
          (s.biUnion fun f => Z.filter (fun v => Incident G v f)) := by
        rw [Finset.disjoint_left]
        intro v hev hvs
        obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvs
        exact (Finset.disjoint_left.mp
          (hb_disjoint (hs (Finset.mem_insert_self e s))
            (hs (Finset.mem_insert_of_mem hf)) (by
              intro heq
              exact hes (by simpa [heq] using hf)))) hev hvf
      rw [Finset.card_union_of_disjoint hd,
        hb_fiber e (hs (Finset.mem_insert_self e s))]
      rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
      rw [Finset.card_insert_of_notMem hes]
      exact Nat.add_comm 1 s.card
  exact aux B (by intro e he; exact he)

private theorem helper_hb_fiber_855.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks;
    let B : Finset E := BoundaryColorEdges G phi Z (↑d : Fin k);
    ∀ e ∈ B, {v ∈ Z | Incident G v e}.card = (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j Ui Uj blocks Z B
  as_aux_lemma =>
  intro e he
  obtain ⟨u, hu, v, hv, huv⟩ := by
    simpa [B, BoundaryColorEdges, BoundaryEdges] using
      (Finset.mem_filter.mp he).1
  have hs : Z.filter (fun x => Incident G x e) = {u} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton, Incident,
      huv, Sym2.mem_iff]
    constructor
    · rintro ⟨hx, rfl | hxe⟩
      · exact rfl
      · exact False.elim (hv (hxe ▸ hx))
    · intro hxu
      subst hxu
      exact ⟨hu, Or.inl rfl⟩
  rw [hs]
  simp

private theorem helper_hAW_898.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks; IsProperEdgeColoring G phi →
    let B : Finset E := BoundaryColorEdges G phi Z (↑d : Fin k);
    let edges : Finset E := {e : E | phi e = some (↑d : Fin k)};
    let good : Finset E := {e ∈ edges |
    ∀ (v : V), Incident G v e → v ∈ Z}; (
    ∀ (e : E), e ∈ edges ↔ phi e = some (↑d : Fin k)) → (
    ∀ (e : E), e ∈ good ↔ e ∈ edges ∧
    ∀ (v : V), Incident G v e → v ∈ Z) →
    let A : Finset V := good.biUnion fun (e : E) ↦ (G.ends e).toFinset;
    let W : Finset V := B.biUnion fun (e : E) ↦ {v ∈ Z | Incident G v e}; Disjoint A W := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j Ui Uj blocks Z hproper B edges good hedge_mem
      hgood A W
  as_aux_lemma =>
  rw [Finset.disjoint_left]
  intro v hvA hvW
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvA
  obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvW
  have hef : e ≠ f := by
    intro hef
    subst hef
    obtain ⟨u, hu, w, hw, huw⟩ := by
      simpa [B, BoundaryColorEdges, BoundaryEdges] using
        (Finset.mem_filter.mp hf).1
    have : w ∈ Z := (hgood e).mp he |>.2 w
      (by change w ∈ G.ends e; rw [huw]; simp)
    exact hw this
  exact (hproper hef ⟨v, Sym2.mem_toFinset.mp hve,
    (Finset.mem_filter.mp hvf).2⟩
    ((hedge_mem e).mp ((hgood e).mp he).1))
    (Finset.mem_filter.mp hf).2

private theorem helper_hextra_974.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R :
        ScheideDefectiveReturnData G k e0 phi T C D d),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let j : Fin C.s := R.blockIndex;
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks;
    let B : Finset E := BoundaryColorEdges G phi Z (↑d : Fin k); D.f0 d ≠ R.f1 → (3 : ℕ) ≤ B.card
        →
    ∃ f ∈ B, f ≠ D.f0 d ∧ f ≠ R.f1 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j Ui Uj blocks Z B hf01 hBthree
  by_contra h
  push Not at h
  have hsub : B ⊆ {D.f0 d, R.f1} := by
    intro f hf
    by_cases hfd : f = D.f0 d
    · simp [hfd]
    · have hfr : f = R.f1 := h f hf hfd
      simp [hfr]
  have hc := Finset.card_le_card hsub
  have hp : ({D.f0 d, R.f1} : Finset E).card = 2 := by simp [hf01]
  rw [hp] at hc
  omega

private theorem helper_continuation_1024.{u_1, u_2} :
    helperContinuation1024Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ phi1 K phi2 psi1 KJ psi2 Ui Uj blocks
      Z horder block_mem_X base_mem_Z hj01 hblocksSub hv1Z f2 hf2f0 hf2f1 hf2color z2 hz2Z u2
      hu2Z hf2ends hz2X hz2v0 hz2v1 hu2u0 hu2u1 hKtree hproperJ1 hstableJ1 hfixedJ1 hKJtree
      hproperJ2 honeJ2 hdeltaMissingJ2 hf0colorJ2 hphi1f2 hpsi1f2 component_vertex_of_edge
      componentJ_vertex_of_edge
  have hf2NotK : Sum.inr f2 ∉ K := by
    intro hf2K
    have hz2K := component_vertex_of_edge hf2K
      (show Incident G z2 f2 by simp [Incident, hf2ends])
      (Or.inr hphi1f2)
    exact hz2v0 ((hKtree z2 hz2X).mp hz2K)
  have hf2NotKJ : Sum.inr f2 ∉ KJ := by
    intro hf2K
    have hz2K := componentJ_vertex_of_edge hf2K
      (show Incident G z2 f2 by simp [Incident, hf2ends])
      (Or.inr hpsi1f2)
    exact hz2v1 ((hKJtree z2 hz2X).mp hz2K)
  have hphi2f2 : phi2 f2 = some d.1 := by
    simp [phi2, TwoColorComponentSwap, K, hf2NotK, hphi1f2]
  have hpsi2f2 : psi2 f2 = some d.1 := by
    simp [psi2, TwoColorComponentSwap, KJ, hf2NotKJ, hpsi1f2]
  have hu2Ui : u2 ∉ Ui := by
    intro hu2Ui
    have hno := ScheideDefectiveNoCross G k e0 phi T C D d f2 hf2color
    apply hno
    refine ⟨u2, hu2Ui, by simp [Incident, hf2ends], z2, ?_, ?_⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨hz2X, ?_⟩
      intro hz2Ui
      exact (Finset.mem_sdiff.mp hz2Z).2
        (Finset.mem_union.mpr (Or.inl hz2Ui))
    · simp [Incident, hf2ends]
  have tashkinov_adjoin := @SharedFacts.ScheideDefectiveThirdBoundaryEdge.tashkinov_adjoin V E
      inferInstance inferInstance
      inferInstance inferInstance G k e0 phi T C D d R
  have adjoin_vertex_set (A0 A1 : TreeSequence G e0) (f : E) (x y : V)
      (hxy : G.ends f = s(x, y)) (hxA : x ∈ TreeSequenceVertexSet A0)
      (hyA : y ∉ TreeSequenceVertexSet A0)
      (hAA : TreeSequenceAdjoinEdge A0 f A1) :
      TreeSequenceVertexSet A1 = insert y (TreeSequenceVertexSet A0) := by
    exact @helper_adjoin_vertex_set_647 V E inferInstance G e0 A0 A1 f x y hxy hyA hAA
  have hu2Uj := @helper_hu2Uj_695 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D d R horder block_mem_X base_mem_Z hj01 hblocksSub hv1Z f2 z2 hz2Z u2 hu2Z hf2ends
      hz2X hu2u0 hu2u1 hproperJ1 hstableJ1 hfixedJ1 hproperJ2 honeJ2 hdeltaMissingJ2 hf0colorJ2
      hpsi2f2 hu2Ui tashkinov_adjoin adjoin_vertex_set
  have hu2X : u2 ∉ X := by
    intro hu2X
    have huBlocks : u2 ∈ blocks := by
      by_contra huBlocks
      exact hu2Z (Finset.mem_sdiff.mpr ⟨hu2X, huBlocks⟩)
    rcases Finset.mem_union.mp huBlocks with huUi | huUj
    · exact hu2Ui huUi
    · exact hu2Uj huUj
  have hz2Target : z2 ∈ TreeSequenceVertexSet T \
      ({C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1} ∪
        {C.blockVertex R.blockIndex 0,
          C.blockVertex R.blockIndex 1}) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨by simpa [X] using hz2X, ?_⟩
    intro hzblocks
    exact (Finset.mem_sdiff.mp hz2Z).2
      (by simpa [blocks, Ui, Uj, i, j] using hzblocks)
  exact ⟨f2, z2, u2, hf2color, hf2ends, hz2Target,
    by simpa [X] using hu2X, hf2f0, hf2f1, hz2v0, hz2v1,
    hphi2f2, hpsi2f2, hu2u0, hu2u1⟩

private theorem helper_continuation_1022.{u_1, u_2} :
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
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let _ : Set (V ⊕ E) := TwoColorComponent G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k) (Sum.inl
        R.v1);
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks; IsProperEdgeColoring G phi → TashkinovOrder G =
        (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd
        (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) → (
    ∀ (r : Fin C.s) (b : Fin (2 : ℕ)), C.blockVertex r b ∈ X) → (
    ∀ (a : Fin C.p), C.y a ∈ Z) → C.blockVertex j (0 : Fin (2 : ℕ)) ≠ C.blockVertex j (1 : Fin (2
        : ℕ)) → blocks ⊆ X →
    let B : Finset E := BoundaryColorEdges G phi Z (↑d : Fin k); Odd B.card → D.v0 d ∈ Z → R.v1 ∈
        Z →
    ∃ (f2 : E) (z2 : V) (u2 : V), phi f2 = some (↑d : Fin k) ∧ G.ends f2 = s(z2, u2) ∧ z2 ∈
        TreeSequenceVertexSet T \ ({C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪ {C.blockVertex R.blockIndex (0 : Fin
        (2 : ℕ)), C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))}) ∧ u2 ∉ TreeSequenceVertexSet T ∧
        f2 ≠ D.f0 d ∧ f2 ≠ R.f1 ∧ z2 ≠ D.v0 d ∧ z2 ≠ R.v1 ∧ TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f2 = some (↑d : Fin k) ∧ TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma
        R.blockIndex) (↑d : Fin k) (Sum.inl R.v1) f2 = some (↑d : Fin k) ∧ u2 ≠ D.u0 d ∧ u2 ≠ R.u1
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ phi1 K phi2 psi1 KJ psi2 Ui Uj blocks
      Z hproper horder block_mem_X base_mem_Z hj01 hblocksSub B hBodd hv0Z hv1Z
  have hf0B : D.f0 d ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, D.f0_color d⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨D.v0 d, hv0Z, D.u0 d,
      fun h => D.u0_outside d (Finset.mem_sdiff.mp h).1, D.f0_ends d⟩
  have hf1B : R.f1 ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, R.f1_color⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R.v1, hv1Z, R.u1,
      fun h => R.u1_outside (Finset.mem_sdiff.mp h).1, R.f1_ends⟩
  have hf01 : D.f0 d ≠ R.f1 := by
    intro h
    have hends : s(D.v0 d, D.u0 d) = s(R.v1, R.u1) := by
      rw [← D.f0_ends d, h, R.f1_ends]
    rcases Sym2.eq_iff.mp hends with hs | hs
    · exact R.v1_ne_v0 hs.1.symm
    · exact R.u1_outside (hs.1 ▸ (Finset.mem_sdiff.mp hv0Z).1)
  have hBtwo : 2 ≤ B.card := by
    have hsub : ({D.f0 d, R.f1} : Finset E) ⊆ B := by
      intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hf0B
      · exact hf1B
    have hc := Finset.card_le_card hsub
    simpa [hf01] using hc
  have hBthree : 3 ≤ B.card := by
    rcases hBodd with ⟨q, hq⟩
    omega
  have hextra := @helper_hextra_974 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R hf01 hBthree
  obtain ⟨f2, hf2B, hf2f0, hf2f1⟩ := hextra
  have hf2color : phi f2 = some d.1 := (Finset.mem_filter.mp hf2B).2
  have hf2boundary : f2 ∈ BoundaryEdges G Z :=
    (Finset.mem_filter.mp hf2B).1
  obtain ⟨z2, hz2Z, u2, hu2Z, hf2ends⟩ := by
    simpa [BoundaryEdges] using hf2boundary
  have hz2X : z2 ∈ X := (Finset.mem_sdiff.mp hz2Z).1
  have hz2v0 : z2 ≠ D.v0 d := by
    intro h
    exact hproper hf2f0
      ⟨z2, by simp [Incident, hf2ends], by simp [Incident, D.f0_ends d, h]⟩
      hf2color (D.f0_color d)
  have hz2v1 : z2 ≠ R.v1 := by
    intro h
    exact hproper hf2f1
      ⟨z2, by simp [Incident, hf2ends], by simp [Incident, R.f1_ends, h]⟩
      hf2color R.f1_color
  have hu2u0 : u2 ≠ D.u0 d := by
    intro h
    exact hproper hf2f0
      ⟨u2, by simp [Incident, hf2ends], by simp [Incident, D.f0_ends d, h]⟩
      hf2color (D.f0_color d)
  have hu2u1 : u2 ≠ R.u1 := by
    intro h
    exact hproper hf2f1
      ⟨u2, by simp [Incident, hf2ends], by simp [Incident, R.f1_ends, h]⟩
      hf2color R.f1_color
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
  have hf2Incident : TreeIncidentEdge T f2 :=
    ⟨z2, hz2X, by simp [Incident, hf2ends]⟩
  have hphi1f2 : phi1 f2 = some d.1 :=
    (hfixed1 f2 hf2Incident).trans hf2color
  have hpsi1f2 : psi1 f2 = some d.1 :=
    (hfixedJ1 f2 hf2Incident).trans hf2color
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
  have componentJ_vertex_of_edge {v : V} {e : E}
      (heK : Sum.inr e ∈ KJ) (hve : Incident G v e)
      (hecolor : psi1 e = some gammaJ ∨ psi1 e = some d.1) :
      Sum.inl v ∈ KJ := by
    let H := TwoColorIncidenceGraph G psi1 gammaJ d.1
    have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
      simpa [H, TwoColorIncidenceGraph] using ⟨hve, hecolor⟩
    change H.connectedComponentMk (Sum.inr e) =
      H.connectedComponentMk (Sum.inl R.v1) at heK
    change H.connectedComponentMk (Sum.inl v) =
      H.connectedComponentMk (Sum.inl R.v1)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heK
  exact @helper_continuation_1024 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R horder block_mem_X base_mem_Z hj01 hblocksSub hv1Z f2 hf2f0 hf2f1 hf2color
      z2 hz2Z u2 hu2Z hf2ends hz2X hz2v0 hz2v1 hu2u0 hu2u1 hKtree hproperJ1 hstableJ1 hfixedJ1
      hKJtree hproperJ2 honeJ2 hdeltaMissingJ2 hf0colorJ2 hphi1f2 hpsi1f2
      component_vertex_of_edge componentJ_vertex_of_edge
private theorem helper_continuation_919.{u_1, u_2} :
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
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let psi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi gamma gammaJ;
    let _ : Set (V ⊕ E) := TwoColorComponent G psi1 gammaJ (↑d : Fin k) (Sum.inl R.v1);
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G psi1 gammaJ (↑d : Fin k) (Sum.inl
        R.v1);
    let Ui : Finset V := {C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex i (1 : Fin (2 : ℕ))};
    let Uj : Finset V := {C.blockVertex j (0 : Fin (2 : ℕ)), C.blockVertex j (1 : Fin (2 : ℕ))};
    let blocks : Finset V := Ui ∪ Uj;
    let Z : Finset V := X \ blocks; IsProperEdgeColoring G phi → TashkinovOrder G =
        (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd
        (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) → ColoredVertexSetClosed G phi
        X → (
    ∀ (r : Fin C.s) (b : Fin (2 : ℕ)), C.blockVertex r b ∈ X) → (
    ∀ (a : Fin C.p), C.y a ∈ Z) → C.blockVertex j (0 : Fin (2 : ℕ)) ≠ C.blockVertex j (1 : Fin (2
        : ℕ)) → blocks ⊆ X → Z.card = X.card - (4 : ℕ) → Odd Z.card →
    let _ : Finset E := BoundaryColorEdges G phi Z (↑d : Fin k);
    let _ : Finset E := {e : E | phi e = some (↑d : Fin k)};
    ∃ (f2 : E) (z2 : V) (u2 : V), phi f2 = some (↑d : Fin k) ∧ G.ends f2 = s(z2, u2) ∧ z2 ∈
        TreeSequenceVertexSet T \ ({C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)),
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} ∪ {C.blockVertex R.blockIndex (0 : Fin
        (2 : ℕ)), C.blockVertex R.blockIndex (1 : Fin (2 : ℕ))}) ∧ u2 ∉ TreeSequenceVertexSet T ∧
        f2 ≠ D.f0 d ∧ f2 ≠ R.f1 ∧ z2 ≠ D.v0 d ∧ z2 ≠ R.v1 ∧ TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f2 = some (↑d : Fin k) ∧ TwoColorComponentSwap G
        (OutsideTreeColorSwap T phi (C.gamma (D.gammaIndex d)) (C.gamma R.blockIndex)) (C.gamma
        R.blockIndex) (↑d : Fin k) (Sum.inl R.v1) f2 = some (↑d : Fin k) ∧ u2 ≠ D.u0 d ∧ u2 ≠ R.u1
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R X i j gamma gammaJ phi1 K phi2 psi1 KJ psi2 Ui Uj blocks
      Z hproper horder hclosed block_mem_X base_mem_Z hj01 hblocksSub hZcard hZodd B edges
  let good := edges.filter (fun e => ∀ v, Incident G v e → v ∈ Z)
  have hdefective : 2 ≤
      (BoundaryColorEdges G phi X d.1).card := by
    have hd := d.property
    change d.1 ∈ (Finset.univ : Finset (Fin k)).filter
      (fun alpha => DefectiveColor G phi X alpha) at hd
    exact (Finset.mem_filter.mp hd).2
  have hpresent : ∀ v, v ∈ Z → d.1 ∈ PresentColors G phi v := by
    intro v hvZ
    have hBpos : 0 < (BoundaryColorEdges G phi X d.1).card := by
      omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hBpos
    have hbb : b ∈ BoundaryEdges G X := (Finset.mem_filter.mp hb).1
    have hbc : phi b = some d.1 := (Finset.mem_filter.mp hb).2
    have hn : d.1 ∉ MissingColors G phi v := by
      exact hclosed hbb (Finset.mem_sdiff.mp hvZ).1 hbc
    simpa [MissingColors] using hn
  have hedge_mem : ∀ e, e ∈ edges ↔ phi e = some d.1 := by
    intro e
    simp [edges]
  have hgood : ∀ e, e ∈ good ↔
      e ∈ edges ∧ ∀ v, Incident G v e → v ∈ Z := by
    intro e
    simp [good]
  have hendcard : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd)
      (Sym2.diag_diagElem hd).symm
  have hgood_disjoint : ∀ ⦃e⦄, e ∈ good → ∀ ⦃f⦄, f ∈ good →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef
      ⟨v, Sym2.mem_toFinset.mp hev, Sym2.mem_toFinset.mp hvf⟩
      ((hedge_mem e).mp ((hgood e).mp he).1))
      ((hedge_mem f).mp ((hgood f).mp hf).1)
  have hgood_union := @helper_hgood_union_640 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R hendcard hgood_disjoint
  have hgood_cover := @helper_hgood_cover_665 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d R hpresent hedge_mem hgood
  have hb_fiber := @helper_hb_fiber_855 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 phi T C D d R
  have hb_disjoint : ∀ ⦃e⦄, e ∈ B → ∀ ⦃f⦄, f ∈ B →
      e ≠ f → Disjoint (Z.filter (fun v => Incident G v e))
        (Z.filter (fun v => Incident G v f)) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef ⟨v, (Finset.mem_filter.mp hev).2,
      (Finset.mem_filter.mp hvf).2⟩
      (Finset.mem_filter.mp he).2) (Finset.mem_filter.mp hf).2
  have hb_union := @helper_hb_union_724 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 phi T C D d R hb_fiber hb_disjoint
  let A := good.biUnion (fun e => (G.ends e).toFinset)
  let W := B.biUnion (fun e => Z.filter (fun v => Incident G v e))
  have hA : A ⊆ Z := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact (hgood e).mp he |>.2 v (Sym2.mem_toFinset.mp hve)
  have hW : W ⊆ Z := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hve).1
  have hAW := @helper_hAW_898 V E inferInstance inferInstance inferInstance inferInstance G k e0 phi
      T C D d R hproper hedge_mem hgood
  have hAZ : A ∪ W = Z := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hA hW
    · intro v hv
      rcases hgood_cover v hv with hvA | hvB
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · exact Finset.mem_union.mpr (Or.inr hvB)
  have hcardeq : Z.card = 2 * good.card + B.card := by
    rw [← hAZ, Finset.card_union_of_disjoint hAW, hgood_union, hb_union]
  have hBodd : Odd B.card := by
    rcases hZodd with ⟨q, hq⟩
    have hq' : Z.card = 2 * q + 1 := by exact hq
    have hqgood : good.card ≤ q := by omega
    refine ⟨q - good.card, ?_⟩
    omega
  have hv0Z : D.v0 d ∈ Z := by
    have hv0base := ScheideStructuralExitsInBase G k e0 phi T C
      (D.v0_is_exit d)
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv0base
    rw [← ha]
    exact base_mem_Z a
  have hv1Z : R.v1 ∈ Z := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp R.v1_in_base
    rw [← ha]
    exact base_mem_Z a
  exact @helper_continuation_1022 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R hproper horder block_mem_X base_mem_Z hj01 hblocksSub hBodd hv0Z hv1Z
theorem ScheideDefectiveThirdBoundaryEdge {V E : Type*}
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
    let Z :=
      TreeSequenceVertexSet T \
        ({C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} ∪
          {C.blockVertex R.blockIndex 0, C.blockVertex R.blockIndex 1})
    ∃ f2 : E,
    ∃ z2 u2 : V,
    phi f2 = some d.1 ∧
      G.ends f2 = s(z2, u2) ∧
        z2 ∈ Z ∧
          u2 ∉ TreeSequenceVertexSet T ∧
            f2 ≠ D.f0 d ∧
              f2 ≠ R.f1 ∧
                z2 ≠ D.v0 d ∧
                  z2 ≠ R.v1 ∧
                    phi2 f2 = some d.1 ∧ psi2 f2 = some d.1 ∧ u2 ≠ D.u0 d ∧ u2 ≠ R.u1 := by
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
  let Ui := ({C.blockVertex i 0, C.blockVertex i 1} : Finset V)
  let Uj := ({C.blockVertex j 0, C.blockVertex j 1} : Finset V)
  let blocks := Ui ∪ Uj
  let Z := X \ blocks
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hclosed0 : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact hclosed0
  have hlength := C.length_eq
  have hij : i ≠ j := by
    simpa [i, j] using R.blockIndex_ne.symm
  have block_vertex_injective := @helper_block_vertex_injective_478 V E inferInstance inferInstance
      inferInstance G k e0 phi T C hlength
  have block_vertex_ne_of_index_ne (r s : Fin C.s) (b c : Fin 2)
      (hrs : r ≠ s) : C.blockVertex r b ≠ C.blockVertex s c := by
    intro h
    have hp : (r, b) = (s, c) := block_vertex_injective h
    exact hrs (congrArg Prod.fst hp)
  have block_pair_ne (r : Fin C.s) :
      C.blockVertex r 0 ≠ C.blockVertex r 1 := by
    intro h
    have hp : (r, (0 : Fin 2)) = (r, (1 : Fin 2)) :=
      block_vertex_injective h
    have hs := congrArg (fun q => q.2.val) hp
    simp at hs
  have block_mem_X (r : Fin C.s) (b : Fin 2) :
      C.blockVertex r b ∈ X := by
    rw [← C.block_vertex_position r b]
    simp [X, TreeSequenceVertexSet]
  have base_ne_block := @helper_base_ne_block_526 V E inferInstance inferInstance inferInstance G k
      e0 phi T C hlength
  have base_mem_Z (a : Fin C.p) : C.y a ∈ Z := by
    have haX : C.y a ∈ X := by
      rw [← C.base_vertex_position a]
      simp [X, TreeSequenceVertexSet]
    apply Finset.mem_sdiff.mpr
    refine ⟨haX, ?_⟩
    simp [blocks, Ui, Uj, base_ne_block]
  have hi01 := block_pair_ne i
  have hj01 := block_pair_ne j
  have hi0j0 := block_vertex_ne_of_index_ne i j 0 0 hij
  have hi0j1 := block_vertex_ne_of_index_ne i j 0 1 hij
  have hi1j0 := block_vertex_ne_of_index_ne i j 1 0 hij
  have hi1j1 := block_vertex_ne_of_index_ne i j 1 1 hij
  have hUiCard : Ui.card = 2 := by simp [Ui, hi01]
  have hUjCard : Uj.card = 2 := by simp [Uj, hj01]
  have hUiUj : Disjoint Ui Uj := by
    rw [Finset.disjoint_left]
    intro v hvi hvj
    simp only [Ui, Uj, Finset.mem_insert, Finset.mem_singleton] at hvi hvj
    rcases hvi with rfl | rfl <;> rcases hvj with hvj | hvj
    · exact hi0j0 hvj
    · exact hi0j1 hvj
    · exact hi1j0 hvj
    · exact hi1j1 hvj
  have hblocksCard : blocks.card = 4 := by
    change (Ui ∪ Uj).card = 4
    rw [Finset.card_union_of_disjoint hUiUj, hUiCard, hUjCard]
  have hblocksSub : blocks ⊆ X := by
    intro v hv
    simp only [blocks, Ui, Uj, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hv
    rcases hv with (rfl | rfl) | rfl | rfl
    · exact block_mem_X i 0
    · exact block_mem_X i 1
    · exact block_mem_X j 0
    · exact block_mem_X j 1
  have hZcard : Z.card = X.card - 4 := by
    change (X \ blocks).card = X.card - 4
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hblocksSub, hblocksCard]
  have hZodd : Odd Z.card := by
    rcases horder.2.2.1 with ⟨q, hq⟩
    have hfour : 4 ≤ X.card := by
      rw [← hblocksCard]
      exact Finset.card_le_card hblocksSub
    refine ⟨q - 2, ?_⟩
    rw [hZcard]
    have hq' : X.card = 2 * q + 1 := by simpa [X] using hq
    omega
  let B := BoundaryColorEdges G phi Z d.1
  let edges := (Finset.univ : Finset E).filter (fun e => phi e = some d.1)
  exact @helper_continuation_919 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d R hproper horder hclosed block_mem_X base_mem_Z hj01 hblocksSub hZcard hZodd
end GoldbergSeymour

end
