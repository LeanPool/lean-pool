/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AbsorbingVertex
public import LeanPool.GoldbergSeymour.AbsorbingVertices
public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.ElementarySingleBoundaryInterchangeable
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveSwitchEffect
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideReplacementMaximum
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideSymmetricDefectiveInternal
public import LeanPool.GoldbergSeymour.ScheideSymmetricMissingInternal
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TreeUsedColors
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Scheide Replacement Absorbing

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation255Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let U : Finset V := (insert ug0 ({ ug1 } : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree; IsProperEdgeColoring G phi →
        ColoredVertexSetElementary G phi X → ColoredVertexSetClosed G phi X → IsProperEdgeColoring
        G phiD → ColoredVertexSetElementary G phiD XD → ColoredVertexSetClosed G phiD XD → ug0 ∈ X
        → ug1 ∈ X → X = Z ∪ U → XD = Z ∪ (insert R.u1 ({ R.u2 } : Finset V) : Finset V) → Z ⊆ X →
        Z ⊆ XD →
    ∀ (fGamma : E), R.u1 ≠ R.u2 → ug0 ≠ ug1 →
    ∀ ⦃u : V⦄, u ∈ (insert R.u1 ({ R.u2 } : Finset V) : Finset V) → u ∉ X →
    ∀ alpha ∈ MissingColors G phi u,
    ∀ (beta : Fin k), beta ≠ alpha → u ∈ (insert R.u1 ({ R.u2 } : Finset V) : Finset V) → u ∈ XD →
        (
    ∃ (f : E), Incident G u f ∧ phi f = some (↑d : Fin k)) → Incident G u fGamma → alpha ≠ (↑d :
        Fin k) → alpha ≠ gamma →
    ∀ v ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi v → (
    ∀ (c : Fin k), c ≠ gamma → c ≠ (↑d : Fin k) →
    ∀ (f : E), phiD f = some c ↔ phi f = some c) → alpha ∈ MissingColors G phiD u → beta ∈
        MissingColors G phiD v → TwoColorIncidenceGraph G phiD beta alpha = TwoColorIncidenceGraph
        G phi beta alpha → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (w : V), a ≠ b → IsProperEdgeColoring G psi →
        a ∈ MissingColors G psi w → TwoColorPathComponent G psi a b (Sum.inl w)) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (w : V), a ≠ b → IsProperEdgeColoring G psi →
        a ∈ MissingColors G psi w → TwoColorPathComponent G psi b a (Sum.inl w)) → (
    ∀ (psi : PartialEdgeColoring E k) (Y : Finset V) (c : Fin k),
    ∀ w ∈ Y, ColoredVertexSetClosed G psi Y → c ∈ MissingColors G psi w → BoundaryColorEdges G psi
        Y c = ∅) →
    ∃ u_1 ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi u_1 ∧ Sum.inl u_1 ∈
        TwoColorComponent G phi beta alpha (Sum.inl u) ∧
    ∀ w ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi w → w = u_1

private abbrev helperContinuation212Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let U : Finset V := (insert ug0 ({ ug1 } : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree; IsProperEdgeColoring G phi →
        ColoredVertexSetElementary G phi X → ColoredVertexSetClosed G phi X → IsProperEdgeColoring
        G phiD → ColoredVertexSetElementary G phiD XD → ColoredVertexSetClosed G phiD XD → ug0 ∈ X
        → ug1 ∈ X → X = Z ∪ U → XD = Z ∪ (insert R.u1 ({ R.u2 } : Finset V) : Finset V) → Z ⊆ X →
        Z ⊆ XD → gamma ≠ (↑d : Fin k) →
    ∀ (fGamma : E), R.u1 ≠ R.u2 → ug0 ≠ ug1 →
    ∀ ⦃u : V⦄, u ∈ (insert R.u1 ({ R.u2 } : Finset V) : Finset V) → u ∉ X →
    ∀ alpha ∈ MissingColors G phi u,
    ∀ (beta : Fin k), beta ≠ alpha → u ∈ (insert R.u1 ({ R.u2 } : Finset V) : Finset V) → u ∈ XD →
        (
    ∃ (f : E), Incident G u f ∧ phi f = some (↑d : Fin k)) → Incident G u fGamma → alpha ≠ (↑d :
        Fin k) → alpha ≠ gamma → beta ∈ TreeMissingColors phi T ∧ beta ∉ TreeUsedColors phi T →
    ∀ v ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi v → gamma ∈ TreeUsedColors phi T →
    ∃ u_1 ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi u_1 ∧ Sum.inl u_1 ∈
        TwoColorComponent G phi beta alpha (Sum.inl u) ∧
    ∀ w ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi w → w = u_1

private theorem helper_branch_135.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let U : Finset V := (insert ug0 ({ ug1 } : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree; ColoredVertexSetElementary G phi
        X → IsProperEdgeColoring G phiD → ColoredVertexSetElementary G phiD XD →
        ColoredVertexSetClosed G phiD XD → Z ⊆ XD →
    ∀ ⦃u : V⦄ (alpha beta : Fin k), beta ≠ alpha → u ∈ XD →
    ∀ v ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phiD u →
        beta ∈ MissingColors G phiD v → TwoColorIncidenceGraph G phiD beta alpha =
        TwoColorIncidenceGraph G phi beta alpha → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (w : V), a ≠ b → IsProperEdgeColoring G psi →
        a ∈ MissingColors G psi w → TwoColorPathComponent G psi a b (Sum.inl w)) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (w : V), a ≠ b → IsProperEdgeColoring G psi →
        a ∈ MissingColors G psi w → TwoColorPathComponent G psi b a (Sum.inl w)) → (
    ∀ (psi : PartialEdgeColoring E k) (Y : Finset V) (c : Fin k),
    ∀ w ∈ Y, ColoredVertexSetClosed G psi Y → c ∈ MissingColors G psi w → BoundaryColorEdges G psi
        Y c = ∅) → v ∈ Z →
    ∃ u_1 ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi u_1 ∧ Sum.inl u_1 ∈
        TwoColorComponent G phi beta alpha (Sum.inl u) ∧
    ∀ w ∈ TreeSequenceVertexSet T, beta ∈ MissingColors G phi w → w = u_1 := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X ug0 ug1 U Z XD hXelem hproperD hXDelem
      hXDclosed hZsubXD u alpha beta hBetaAlpha huXD v hvX hBetaMissing hAlphaMissingD
      hBetaMissingD hgraph missingRootPath missingSecondRootPath closedBoundaryEmpty hvZ
  have hvXD : v ∈ XD := hZsubXD hvZ
  have hBetaBoundary : BoundaryColorEdges G phiD XD beta = ∅ :=
    closedBoundaryEmpty phiD XD beta v hvXD hXDclosed hBetaMissingD
  have hAlphaBoundary : BoundaryColorEdges G phiD XD alpha = ∅ :=
    closedBoundaryEmpty phiD XD alpha u huXD hXDclosed hAlphaMissingD
  have hinter : TreeInterchangeable G R.replacementTree phiD beta alpha := by
    apply ElementarySingleBoundaryInterchangeable G phiD R.replacementTree
      beta alpha hproperD hXDelem hBetaBoundary
    rw [show BoundaryColorEdges G phiD
      (TreeSequenceVertexSet R.replacementTree) alpha = ∅ by
        simpa [XD] using hAlphaBoundary]
    simp
  have hpathU : TwoColorPathComponent G phiD beta alpha (Sum.inl u) :=
    missingSecondRootPath phiD alpha beta u hBetaAlpha.symm hproperD hAlphaMissingD
  have hpathV : TwoColorPathComponent G phiD beta alpha (Sum.inl v) :=
    missingRootPath phiD beta alpha v hBetaAlpha hproperD hBetaMissingD
  have hcompEq := hinter (Sum.inl u) (Sum.inl v) hpathU hpathV
    ⟨u, huXD, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
    ⟨v, hvXD, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hvCompD : Sum.inl v ∈
      TwoColorComponent G phiD beta alpha (Sum.inl u) := by
    rw [hcompEq]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  refine ⟨v, by simpa [X] using hvX, hBetaMissing, ?_, ?_⟩
  · unfold TwoColorComponent at hvCompD ⊢
    rw [hgraph] at hvCompD
    exact hvCompD
  · intro w hwX hBetaW
    by_contra hwv
    have hdis := hXelem (by simpa [X] using hvX)
      (by simpa [X] using hwX) (fun h => hwv h.symm)
    exact (Finset.disjoint_left.mp hdis) hBetaMissing hBetaW

private theorem helper_hAlphaBoundaryCard_298.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let ug0 : V := C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ));
    let ug1 : V := C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ));
    let U : Finset V := (insert ug0 ({ ug1 } : Finset V) : Finset V);
    let Z : Finset V := X \ U;
    let XD : Finset V := TreeSequenceVertexSet R.replacementTree; IsProperEdgeColoring G phi →
        ColoredVertexSetClosed G phiD XD → ug0 ∈ X → ug1 ∈ X → X = Z ∪ U → XD = Z ∪ (insert R.u1
        ({ R.u2 } : Finset V) : Finset V) → Z ⊆ X → Z ⊆ XD →
    ∀ ⦃u : V⦄,
    ∀ alpha ∈ MissingColors G phi u, u ∈ XD → alpha ≠ (↑d : Fin k) → alpha ≠ gamma →
    ∀ (v : V), (
    ∀ (c : Fin k), c ≠ gamma → c ≠ (↑d : Fin k) →
    ∀ (f : E), phiD f = some c ↔ phi f = some c) → alpha ∈ MissingColors G phiD u →
    let u' : V := if u = R.u1 then R.u2 else R.u1;
    let v' : V := if v = ug0 then ug1 else ug0; (insert u ({ u' } : Finset V) : Finset V) =
        (insert R.u1 ({ R.u2 } : Finset V) : Finset V) → (insert v ({ v' } : Finset V) : Finset V)
        = (insert ug0 ({ ug1 } : Finset V) : Finset V) → v ≠ v' →
    ∀ (aGamma : E), phi aGamma = some alpha → G.ends aGamma = s(v, v') →
    ∀ (aZ : E), Incident G u' aZ → phi aZ = some alpha → (BoundaryColorEdges G phi X alpha).card ≤
        (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X ug0 ug1 U Z XD hproper hXDclosed hug0X
      hug1X hXsplit hXDsplit hZsubX hZsubXD u alpha hAlpha huXD hAlphaDelta hAlphaGamma v
      colorFixed hAlphaMissingD u' v' hUPair hVPair hVne aGamma haGammaColor haGammaEnds aZ haZU'
      haZColor
  apply (Finset.card_le_card (t := ({aZ} : Finset E)))
  intro q hq
  have hqBoundary : q ∈ BoundaryEdges G X := (Finset.mem_filter.mp hq).1
  have hqColor : phi q = some alpha := (Finset.mem_filter.mp hq).2
  obtain ⟨x, hxX, y, hyX, hqEnds⟩ := by
    simpa [BoundaryEdges] using hqBoundary
  have hxSplit : x ∈ Z ∨ x ∈ U := by
    have hx : x ∈ X := hxX
    rw [hXsplit] at hx
    exact Finset.mem_union.mp hx
  have hxZ : x ∈ Z := by
    rcases hxSplit with hxZ | hxU
    · exact hxZ
    · exfalso
      have hqInc : Incident G x q := by
        change x ∈ G.ends q
        rw [hqEnds]
        simp
      have haInc : Incident G x aGamma := by
        change x ∈ G.ends aGamma
        rw [haGammaEnds]
        have : x ∈ ({v, v'} : Finset V) := by
          rw [hVPair]
          simpa [U] using hxU
        simpa [hVne] using this
      have hqNe : q ≠ aGamma := by
        intro h
        apply hyX
        have hyPair : y ∈ ({v, v'} : Finset V) := by
          have hyInc : Incident G y aGamma := by
            change y ∈ G.ends aGamma
            rw [← h, hqEnds]
            simp
          simpa [Incident, haGammaEnds] using hyInc
        rw [hVPair] at hyPair
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyPair
        rcases hyPair with rfl | rfl
        · exact hug0X
        · exact hug1X
      exact (hproper hqNe ⟨x, hqInc, haInc⟩ hqColor) haGammaColor
  have hxXD : x ∈ XD := hZsubXD hxZ
  have hqColorD : phiD q = some alpha :=
    (colorFixed alpha hAlphaGamma hAlphaDelta q).mpr hqColor
  have hyXD : y ∈ XD := by
    by_contra hy
    have hboundary : q ∈ BoundaryEdges G XD := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxXD, y, hy, hqEnds⟩
    exact hXDclosed hboundary huXD hqColorD hAlphaMissingD
  have hyPair : y ∈ ({R.u1, R.u2} : Finset V) := by
    have hy := hyXD
    rw [hXDsplit] at hy
    rcases Finset.mem_union.mp hy with hyZ | hyPair
    · exact False.elim (hyX (hZsubX hyZ))
    · exact hyPair
  rw [← hUPair] at hyPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyPair
  have hyU' : y = u' := by
    rcases hyPair with hyU | hyU'
    · exfalso
      have hinc : Incident G u q := by
        change u ∈ G.ends q
        rw [hqEnds, ← hyU]
        simp
      have hpresent : alpha ∈ PresentColors G phi u := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨q, hinc, hqColor⟩
      exact (Finset.mem_sdiff.mp hAlpha).2 hpresent
    · exact hyU'
  have hqIncU' : Incident G u' q := by
    change u' ∈ G.ends q
    rw [hqEnds, hyU']
    simp
  have hqaZ : q = aZ := by
    by_contra hne
    exact (hproper hne ⟨u', hqIncU', haZU'⟩ hqColor) haZColor
  simp [hqaZ]

private theorem helper_continuation_255.{u_1, u_2} :
    helperContinuation255Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X ug0 ug1 U Z XD hproper hXelem hXclosed
      hproperD hXDelem hXDclosed hug0X hug1X hXsplit hXDsplit hZsubX hZsubXD fGamma huPairNe
      hugPairNe u hu huOutside alpha hAlpha beta hBetaAlpha huPair huXD huDeltaIncident
      huGammaIncident hAlphaDelta hAlphaGamma v hvX hBetaMissing colorFixed hAlphaMissingD
      hBetaMissingD hgraph missingRootPath missingSecondRootPath closedBoundaryEmpty
  have hvSplit : v ∈ Z ∨ v ∈ U := by
    have hvX' : v ∈ X := by simpa [X] using hvX
    rw [hXsplit] at hvX'
    exact Finset.mem_union.mp hvX'
  rcases hvSplit with hvZ | hvU
  · exact @helper_branch_135 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@hXelem) (@hproperD) (@hXDelem)
      (@hXDclosed) (@hZsubXD) (@u) (@alpha) (@beta) (@hBetaAlpha) (@huXD) (@v) (@hvX)
      (@hBetaMissing) (@hAlphaMissingD) (@hBetaMissingD) (@hgraph) (@missingRootPath)
      (@missingSecondRootPath) (@closedBoundaryEmpty) (@hvZ)
  · let u' : V := if u = R.u1 then R.u2 else R.u1
    let v' : V := if v = ug0 then ug1 else ug0
    have hUPair : ({u, u'} : Finset V) = {R.u1, R.u2} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at huPair
      rcases huPair with hu1 | hu2
      · subst u
        simp [u']
      · subst u
        have hne : R.u2 ≠ R.u1 := huPairNe.symm
        ext x
        simp [u', hne, or_comm]
    have hUne : u ≠ u' := by
      intro h
      have hc : ({u, u'} : Finset V).card = 1 := by simp [h]
      have hr : ({R.u1, R.u2} : Finset V).card = 2 := by simp [huPairNe]
      rw [hUPair, hr] at hc
      omega
    have hVPair : ({v, v'} : Finset V) = {ug0, ug1} := by
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hvU
      rcases hvU with hv0 | hv1
      · subst v
        simp [v']
      · subst v
        have hne : ug1 ≠ ug0 := hugPairNe.symm
        ext x
        simp [v', hne, or_comm]
    have hVne : v ≠ v' := by
      intro h
      have hc : ({v, v'} : Finset V).card = 1 := by simp [h]
      have hr : ({ug0, ug1} : Finset V).card = 2 := by simp [hugPairNe]
      rw [hVPair, hr] at hc
      omega
    have hu'XD : u' ∈ XD := by
      rw [hXDsplit]
      apply Finset.mem_union_right
      rw [← hUPair]
      simp
    have hvX' : v ∈ X := by simpa [X] using hvX
    have hv'X : v' ∈ X := by
      rw [hXsplit]
      apply Finset.mem_union_right
      rw [show U = {v, v'} by simpa [U] using hVPair.symm]
      simp
    have hAlphaPair :
        alpha ∈ MissingColors G phi R.u1 ∨
          alpha ∈ MissingColors G phi R.u2 := by
      have huOrig : u ∈ ({R.u1, R.u2} : Finset V) := by
        rw [← hUPair]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at huOrig
      rcases huOrig with hu1 | hu2
      · exact Or.inl (by simpa [hu1] using hAlpha)
      · exact Or.inr (by simpa [hu2] using hAlpha)
    have hBetaPair :
        beta ∈ MissingColors G phi ug0 ∨
          beta ∈ MissingColors G phi ug1 := by
      have hvPair : v ∈ ({ug0, ug1} : Finset V) := by simpa [U] using hvU
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
      rcases hvPair with rfl | rfl
      · exact Or.inl hBetaMissing
      · exact Or.inr hBetaMissing
    have hmissingInternal := ScheideSymmetricMissingInternal G k e0 phi T C D d R
    obtain ⟨aGamma, haGammaColor, haGammaEnds0⟩ :=
      hmissingInternal.1 alpha hAlphaPair
    obtain ⟨bDelta, hbDeltaColor, hbDeltaEnds0⟩ :=
      hmissingInternal.2 beta hBetaPair
    have haGammaEnds : G.ends aGamma = s(v, v') := by
      rw [show G.ends aGamma = s(ug0, ug1) by
        simpa [ug0, ug1] using haGammaEnds0]
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hvU
      rcases hvU with hv0 | hv1
      · subst v
        simp [v']
      · subst v
        have hne : ug1 ≠ ug0 := hugPairNe.symm
        simp [v', hne, Sym2.eq_swap]
    have hbDeltaEnds : G.ends bDelta = s(u, u') := by
      rw [hbDeltaEnds0]
      have huOrig : u ∈ ({R.u1, R.u2} : Finset V) := by
        rw [← hUPair]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at huOrig
      rcases huOrig with hu1 | hu2
      · subst u
        simp [u']
      · subst u
        have hne : R.u2 ≠ R.u1 := huPairNe.symm
        simp [u', hne, Sym2.eq_swap]
    have hAlphaNotMissingU' : alpha ∉ MissingColors G phiD u' := by
      intro hmiss
      have hdis := hXDelem huXD hu'XD hUne
      exact (Finset.disjoint_left.mp hdis) hAlphaMissingD hmiss
    have hAlphaPresentU' : alpha ∈ PresentColors G phiD u' := by
      simpa [MissingColors] using hAlphaNotMissingU'
    obtain ⟨aZ, haZU', haZColorD⟩ :
        ∃ aZ : E, Incident G u' aZ ∧ phiD aZ = some alpha := by
      simpa [PresentColors] using hAlphaPresentU'
    have haZColor : phi aZ = some alpha :=
      (colorFixed alpha hAlphaGamma hAlphaDelta aZ).mp haZColorD
    obtain ⟨zA, haZEnds⟩ := Sym2.mem_iff_exists.mp haZU'
    have hzANeU' : zA ≠ u' := by
      intro h
      exact G.loopless aZ u' (by simpa [h] using haZEnds)
    have hzAXD : zA ∈ XD := by
      by_contra hzA
      have hboundary : aZ ∈ BoundaryEdges G XD := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u', hu'XD, zA, hzA, haZEnds⟩
      exact hXDclosed hboundary huXD haZColorD hAlphaMissingD
    have hzANeU : zA ≠ u := by
      intro h
      have hinc : Incident G u aZ := by
        change u ∈ G.ends aZ
        rw [haZEnds, h]
        simp
      have hpresent : alpha ∈ PresentColors G phi u := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨aZ, hinc, haZColor⟩
      exact (Finset.mem_sdiff.mp hAlpha).2 hpresent
    have hzAZ : zA ∈ Z := by
      have hz := hzAXD
      rw [hXDsplit] at hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact hz
      · rw [← hUPair] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · exact False.elim (hzANeU hz)
        · exact False.elim (hzANeU' hz)
    have hBetaBoundary : BoundaryColorEdges G phi X beta = ∅ :=
      closedBoundaryEmpty phi X beta v hvX' hXclosed hBetaMissing
    have hAlphaBoundaryCard := @helper_hAlphaBoundaryCard_298 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@hproper)
        (@hXDclosed) (@hug0X) (@hug1X) (@hXsplit) (@hXDsplit) (@hZsubX) (@hZsubXD) (@u) (@alpha)
        (@hAlpha) (@huXD) (@hAlphaDelta) (@hAlphaGamma) (@v) (@colorFixed) (@hAlphaMissingD)
        (@hUPair) (@hVPair) (@hVne) (@aGamma) (@haGammaColor) (@haGammaEnds) (@aZ) (@haZU')
        (@haZColor)
    have hinter : TreeInterchangeable G T phi beta alpha := by
      exact ElementarySingleBoundaryInterchangeable G phi T beta alpha
        hproper hXelem (by simpa [X] using hBetaBoundary)
        (by simpa [X] using hAlphaBoundaryCard)
    have hpathU : TwoColorPathComponent G phi beta alpha (Sum.inl u) :=
      missingSecondRootPath phi alpha beta u hBetaAlpha.symm hproper hAlpha
    have hpathV : TwoColorPathComponent G phi beta alpha (Sum.inl v) :=
      missingRootPath phi beta alpha v hBetaAlpha hproper hBetaMissing
    let H := TwoColorIncidenceGraph G phi beta alpha
    have hAdjUB : H.Adj (Sum.inl u) (Sum.inr bDelta) := by
      simp [H, TwoColorIncidenceGraph, Incident, hbDeltaEnds, hbDeltaColor]
    have hAdjBU' : H.Adj (Sum.inr bDelta) (Sum.inl u') := by
      simp [H, TwoColorIncidenceGraph, Incident, hbDeltaEnds, hbDeltaColor]
    have hAdjU'A : H.Adj (Sum.inl u') (Sum.inr aZ) := by
      simp [H, TwoColorIncidenceGraph, haZU', haZColor]
    have hAdjAZ : H.Adj (Sum.inr aZ) (Sum.inl zA) := by
      have hinc : Incident G zA aZ := by
        change zA ∈ G.ends aZ
        rw [haZEnds]
        simp
      simp [H, TwoColorIncidenceGraph, hinc, haZColor]
    have hzAComp : Sum.inl zA ∈
        TwoColorComponent G phi beta alpha (Sum.inl u) := by
      change H.connectedComponentMk (Sum.inl zA) =
        H.connectedComponentMk (Sum.inl u)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdjAZ).symm.trans
        ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdjU'A).symm.trans
          ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdjBU').symm.trans
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdjUB).symm))
    have hcompEq := hinter (Sum.inl u) (Sum.inl v) hpathU hpathV
      ⟨zA, hZsubX hzAZ, hzAComp⟩
      ⟨v, hvX', SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
    have hvComp : Sum.inl v ∈
        TwoColorComponent G phi beta alpha (Sum.inl u) := by
      rw [hcompEq]
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    refine ⟨v, by simpa [X] using hvX, hBetaMissing, hvComp, ?_⟩
    intro w hwX hBetaW
    by_contra hwv
    have hdis := hXelem (by simpa [X] using hvX)
      (by simpa [X] using hwX) (fun h => hwv h.symm)
    exact (Finset.disjoint_left.mp hdis) hBetaMissing hBetaW

private theorem helper_continuation_212.{u_1, u_2} :
    helperContinuation212Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R gamma phiD X ug0 ug1 U Z XD hproper hXelem hXclosed
      hproperD hXDelem hXDclosed hug0X hug1X hXsplit hXDsplit hZsubX hZsubXD hgammaDelta fGamma
      huPairNe hugPairNe u hu huOutside alpha hAlpha beta hBetaAlpha huPair huXD huDeltaIncident
      huGammaIncident hAlphaDelta hAlphaGamma hBetaData v hvX hBetaMissing hGammaUsed
  have hBetaGamma : beta ≠ gamma := by
    intro h
    exact hBetaData.2 (h ▸ hGammaUsed)
  have hBetaDelta : beta ≠ d.1 := by
    intro h
    have hdcard : 2 ≤ (BoundaryColorEdges G phi X d.1).card := by
      have hd := (Finset.mem_filter.mp d.2).2
      simpa only [DefectiveColor, X] using hd
    obtain ⟨f, hf⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le Nat.zero_lt_two hdcard)
    have := hXclosed (Finset.mem_filter.mp hf).1 (by simpa [X] using hvX)
      (Finset.mem_filter.mp hf).2
    exact this (by simpa [h] using hBetaMissing)
  have colorFixed (c : Fin k) (hcGamma : c ≠ gamma) (hcDelta : c ≠ d.1)
      (f : E) : phiD f = some c ↔ phi f = some c := by
    simp only [phiD, TwoColorComponentSwap]
    by_cases hf : Sum.inr f ∈
        TwoColorComponent G phi gamma d.1 (Sum.inl (D.v0 d))
    · simp only [hf, ite_eq_left]
      by_cases hfg : phi f = some gamma
      · rw [hfg]
        simp only [ite_eq_left]
        constructor
        · intro hnew
          exact False.elim (hcDelta (Option.some.inj hnew).symm)
        · intro hold
          exact False.elim (hcGamma (Option.some.inj hold).symm)
      · by_cases hfd : phi f = some d.1
        · rw [hfd]
          simp only [Option.some.injEq, hgammaDelta.symm, ite_false, ite_eq_left]
          constructor
          · intro hnew
            exact False.elim (hcGamma hnew.symm)
          · intro hold
            exact False.elim (hcDelta hold.symm)
        · simp [hfg, hfd]
    · simp [hf]
  have hAlphaMissingD : alpha ∈ MissingColors G phiD u := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ alpha, ?_⟩
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
    obtain ⟨f, huf, hfc⟩ := hpresent
    exact (Finset.mem_sdiff.mp hAlpha).2 (by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, huf, (colorFixed alpha hAlphaGamma hAlphaDelta f).mp hfc⟩)
  have hBetaMissingD : beta ∈ MissingColors G phiD v := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ beta, ?_⟩
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
    obtain ⟨f, hvf, hfc⟩ := hpresent
    exact (Finset.mem_sdiff.mp hBetaMissing).2 (by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, hvf, (colorFixed beta hBetaGamma hBetaDelta f).mp hfc⟩)
  have hgraph : TwoColorIncidenceGraph G phiD beta alpha =
      TwoColorIncidenceGraph G phi beta alpha := by
    ext x y
    cases x with
    | inl vx =>
        cases y with
        | inl vy => rfl
        | inr e =>
            simp only [TwoColorIncidenceGraph]
            constructor <;> rintro ⟨hi, hc⟩ <;> refine ⟨hi, ?_⟩
            · rcases hc with hc | hc
              · exact Or.inl ((colorFixed beta hBetaGamma hBetaDelta e).mp hc)
              · exact Or.inr ((colorFixed alpha hAlphaGamma hAlphaDelta e).mp hc)
            · rcases hc with hc | hc
              · exact Or.inl ((colorFixed beta hBetaGamma hBetaDelta e).mpr hc)
              · exact Or.inr ((colorFixed alpha hAlphaGamma hAlphaDelta e).mpr hc)
    | inr e =>
        cases y with
        | inl vy =>
            simp only [TwoColorIncidenceGraph]
            constructor <;> rintro ⟨hi, hc⟩ <;> refine ⟨hi, ?_⟩
            · rcases hc with hc | hc
              · exact Or.inl ((colorFixed beta hBetaGamma hBetaDelta e).mp hc)
              · exact Or.inr ((colorFixed alpha hAlphaGamma hAlphaDelta e).mp hc)
            · rcases hc with hc | hc
              · exact Or.inl ((colorFixed beta hBetaGamma hBetaDelta e).mpr hc)
              · exact Or.inr ((colorFixed alpha hAlphaGamma hAlphaDelta e).mpr hc)
        | inr f => rfl
  have missingRootPath :
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (w : V), a ≠ b → IsProperEdgeColoring G psi →
        a ∈ MissingColors G psi w → TwoColorPathComponent G psi a b (Sum.inl w) := by
    intro psi a b w hab hprop hmiss
    refine ⟨hab, Sum.inl w,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem, ?_⟩
    rintro x hx y hy
    have no_a : ∀ e : E, Incident G w e → psi e ≠ some a := by
      intro e hwe hcolor
      have hpresent : a ∈ PresentColors G psi w := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hwe, hcolor⟩
      exact (Finset.mem_sdiff.mp hmiss).2 hpresent
    cases x with
    | inl x =>
        simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx
    | inr e =>
        cases y with
        | inl y =>
            simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hy
        | inr f =>
            apply congrArg Sum.inr
            simp only [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx hy
            have hecolor : psi e = some b := hx.2.resolve_left (no_a e hx.1)
            have hfcolor : psi f = some b := hy.2.resolve_left (no_a f hy.1)
            by_contra hef
            exact (hprop hef ⟨w, hx.1, hy.1⟩ hecolor) hfcolor
  have missingSecondRootPath :
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (w : V), a ≠ b → IsProperEdgeColoring G psi →
        a ∈ MissingColors G psi w → TwoColorPathComponent G psi b a (Sum.inl w) := by
    intro psi a b w hab hprop hmiss
    refine ⟨hab.symm, Sum.inl w,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem, ?_⟩
    rintro x hx y hy
    have no_a : ∀ e : E, Incident G w e → psi e ≠ some a := by
      intro e hwe hcolor
      have hpresent : a ∈ PresentColors G psi w := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hwe, hcolor⟩
      exact (Finset.mem_sdiff.mp hmiss).2 hpresent
    cases x with
    | inl x =>
        simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx
    | inr e =>
        cases y with
        | inl y =>
            simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hy
        | inr f =>
            apply congrArg Sum.inr
            simp only [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx hy
            have hecolor : psi e = some b := hx.2.resolve_right (no_a e hx.1)
            have hfcolor : psi f = some b := hy.2.resolve_right (no_a f hy.1)
            by_contra hef
            exact (hprop hef ⟨w, hx.1, hy.1⟩ hecolor) hfcolor
  have closedBoundaryEmpty :
    ∀ (psi : PartialEdgeColoring E k) (Y : Finset V) (c : Fin k) (w : V), w ∈ Y →
        ColoredVertexSetClosed G psi Y → c ∈ MissingColors G psi w → BoundaryColorEdges G psi Y c
        = ∅ := by
    intro psi Y c w hwY hclosed hmiss
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    exact hclosed (Finset.mem_filter.mp he).1 hwY
      (Finset.mem_filter.mp he).2 hmiss
  exact @helper_continuation_255 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@hproper) (@hXelem)
      (@hXclosed) (@hproperD) (@hXDelem) (@hXDclosed) (@hug0X) (@hug1X) (@hXsplit) (@hXDsplit)
      (@hZsubX) (@hZsubXD) (@fGamma) (@huPairNe) (@hugPairNe) (@u) (@hu) (@huOutside) (@alpha)
      (@hAlpha) (@beta) (@hBetaAlpha) (@huPair) (@huXD) (@huDeltaIncident) (@huGammaIncident)
      (@hAlphaDelta) (@hAlphaGamma) (@v) (@hvX) (@hBetaMissing) (@colorFixed) (@hAlphaMissingD)
      (@hBetaMissingD) (@hgraph) (@missingRootPath) (@missingSecondRootPath) (@closedBoundaryEmpty)
theorem ScheideReplacementAbsorbing {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    {R.u1, R.u2} ⊆ AbsorbingVertices T phi := by
  classical
  let gamma := C.gamma (D.gammaIndex d)
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let X := TreeSequenceVertexSet T
  let ug0 := C.blockVertex (D.gammaIndex d) 0
  let ug1 := C.blockVertex (D.gammaIndex d) 1
  let U := ({ug0, ug1} : Finset V)
  let Z := X \ U
  let XD := TreeSequenceVertexSet R.replacementTree
  have hproper : IsProperEdgeColoring G phi := C.globally_maximum.1.2.2.2.1
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hXelem : ColoredVertexSetElementary G phi X := by
    exact horder.2.2.2.1
  have hXclosed : ColoredVertexSetClosed G phi X := by
    exact horder.2.2.2.2
  have hrep := ScheideReplacementMaximum G k e0 phi T C D d R
  have hproperD : IsProperEdgeColoring G phiD := by
    simpa [gamma, phiD] using hrep.1
  have hrepGlobal : GlobalMaximumTriple G k e0 phiD R.replacementTree := by
    simpa [gamma, phiD] using hrep.2.2
  have horderD := ScheideGlobalMaximumOrder G k e0 phiD R.replacementTree hrepGlobal
  have hXDelem : ColoredVertexSetElementary G phiD XD := by
    exact horderD.2.2.2.1
  have hXDclosed : ColoredVertexSetClosed G phiD XD := by
    exact horderD.2.2.2.2
  have hug0X : ug0 ∈ X := by
    change C.blockVertex (D.gammaIndex d) 0 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hug1X : ug1 ∈ X := by
    change C.blockVertex (D.gammaIndex d) 1 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (1 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hXsplit : X = Z ∪ U := by
    ext x
    simp only [Z, Finset.mem_union, Finset.mem_sdiff, U]
    by_cases hx : x ∈ X
    · by_cases hu : x ∈ ({ug0, ug1} : Finset V) <;> simp [hx, hu]
    · have hnu : x ∉ ({ug0, ug1} : Finset V) := by
        intro hxu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxu
        rcases hxu with rfl | rfl <;> contradiction
      simp [hx, hnu]
  have hXDsplit : XD = Z ∪ {R.u1, R.u2} := by
    simpa [XD, X, Z, U, ug0, ug1] using R.replacement_vertices
  have hu1XD : R.u1 ∈ XD := by rw [hXDsplit]; simp
  have hu2XD : R.u2 ∈ XD := by rw [hXDsplit]; simp
  have hZsubX : Z ⊆ X := by
    intro z hz
    exact (Finset.mem_sdiff.mp hz).1
  have hZsubXD : Z ⊆ XD := by
    intro z hz
    rw [hXDsplit]
    exact Finset.mem_union_left _ hz
  have hgammaDelta : gamma ≠ d.1 := by
    intro heq
    have hmissing : gamma ∈ MissingColors G phi (D.v0 d) := by
      simpa [gamma] using D.gamma_missing_at_v0 d
    have hinc : Incident G (D.v0 d) (D.f0 d) := by
      change D.v0 d ∈ G.ends (D.f0 d)
      rw [D.f0_ends]
      simp
    have hpresent : gamma ∈ PresentColors G phi (D.v0 d) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨D.f0 d, hinc, by simpa [heq] using D.f0_color d⟩
    exact (Finset.mem_sdiff.mp hmissing).2 hpresent
  obtain ⟨fGamma, hfGammaColor, hfGammaEnds⟩ :=
    (ScheideSymmetricDefectiveInternal G k e0 phi T C D d R).2
  have huPairNe : R.u1 ≠ R.u2 := by
    intro h
    have hi := R.replacementTree.vertex_injective
      (R.replacement_last_vertices.1.trans
        (h.trans R.replacement_last_vertices.2.symm))
    have hv : T.length - 1 = T.length := by
      simpa using congrArg Fin.val hi
    have hp := T.positive
    omega
  have hugPairNe : ug0 ≠ ug1 := by
    intro h
    let q0 : Fin (T.length + 1) := ⟨C.p + 2 * (D.gammaIndex d).val, by
      have hi := (D.gammaIndex d).isLt
      have hl := C.length_eq
      omega⟩
    let q1 : Fin (T.length + 1) := ⟨C.p + 2 * (D.gammaIndex d).val + 1, by
      have hi := (D.gammaIndex d).isLt
      have hl := C.length_eq
      omega⟩
    have hv : T.vertex q0 = T.vertex q1 := by
      rw [show T.vertex q0 = ug0 by
        simpa [q0, ug0] using C.block_vertex_position (D.gammaIndex d) 0]
      rw [show T.vertex q1 = ug1 by
        simpa [q1, ug1] using C.block_vertex_position (D.gammaIndex d) 1]
      exact h
    have hq := congrArg Fin.val (T.vertex_injective hv)
    dsimp [q0, q1] at hq
    omega
  intro u hu
  simp only [AbsorbingVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  have huOutside : u ∉ X := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact R.u1_outside
    · exact R.u2_outside
  refine ⟨by simpa [X] using huOutside, ?_⟩
  intro alpha hAlpha beta hBeta hBetaAlpha
  have huPair : u ∈ ({R.u1, R.u2} : Finset V) := by simpa using hu
  have huXD : u ∈ XD := by
    rw [hXDsplit]
    exact Finset.mem_union_right _ huPair
  have huDeltaIncident : ∃ f : E, Incident G u f ∧ phi f = some d.1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at huPair
    rcases huPair with rfl | rfl
    · refine ⟨R.f1, ?_, R.f1_color⟩
      change R.u1 ∈ G.ends R.f1
      rw [R.f1_ends]
      simp
    · refine ⟨R.f2, ?_, R.f2_color⟩
      change R.u2 ∈ G.ends R.f2
      rw [R.f2_ends]
      simp
  have huGammaIncident : Incident G u fGamma := by
    change u ∈ G.ends fGamma
    rw [hfGammaEnds]
    simpa [huPairNe] using huPair
  have hAlphaDelta : alpha ≠ d.1 := by
    rintro rfl
    obtain ⟨f, huf, hfc⟩ := huDeltaIncident
    have hpresent : d.1 ∈ PresentColors G phi u := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, huf, hfc⟩
    exact (Finset.mem_sdiff.mp hAlpha).2 hpresent
  have hAlphaGamma : alpha ≠ gamma := by
    rintro rfl
    have hpresent : gamma ∈ PresentColors G phi u := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fGamma, huGammaIncident, by simpa [gamma] using hfGammaColor⟩
    exact (Finset.mem_sdiff.mp hAlpha).2 hpresent
  have hBetaData := Finset.mem_sdiff.mp hBeta
  obtain ⟨v, hvX, hBetaMissing⟩ := Finset.mem_biUnion.mp hBetaData.1
  have hGammaUsed : gamma ∈ TreeUsedColors phi T := by
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
    let j : Fin T.length := ⟨C.p - 1 + 2 * (D.gammaIndex d).val, by
      have hi := (D.gammaIndex d).isLt
      have hp := C.p_ge_two
      have hl := C.length_eq
      omega⟩
    refine ⟨j, ?_, ?_⟩
    · dsimp [j]
      have hp := C.p_ge_two
      omega
    rw [show T.edge j = C.blockEdge (D.gammaIndex d) (0 : Fin 2) by
      simpa [j] using C.block_edge_position (D.gammaIndex d) 0]
    simpa [gamma] using C.block_color (D.gammaIndex d) 0
  exact @helper_continuation_212 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@hproper) (@hXelem)
      (@hXclosed) (@hproperD) (@hXDelem) (@hXDclosed) (@hug0X) (@hug1X) (@hXsplit) (@hXDsplit)
      (@hZsubX) (@hZsubXD) (@hgammaDelta) (@fGamma) (@huPairNe) (@hugPairNe) (@u) (@hu)
      (@huOutside) (@alpha) (@hAlpha) (@beta) (@hBetaAlpha) (@huPair) (@huXD) (@huDeltaIncident)
      (@huGammaIncident) (@hAlphaDelta) (@hAlphaGamma) (@hBetaData) (@v) (@hvX) (@hBetaMissing)
      (@hGammaUsed)
end GoldbergSeymour

end
