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
public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainBoundaryEdges
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPath
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPathExists
public import LeanPool.GoldbergSeymour.ScheideDefectiveNoCross
public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideDefectiveSwitchEffect
public import LeanPool.GoldbergSeymour.ScheideExitNoFree
public import LeanPool.GoldbergSeymour.ScheideExitVertex
public import LeanPool.GoldbergSeymour.ScheideExitVertices
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideReplacementInternalMissing
public import LeanPool.GoldbergSeymour.ScheideReplacementMaximum
public import LeanPool.GoldbergSeymour.ScheideReplacementPairFixed
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralExitsInBase
public import LeanPool.GoldbergSeymour.ScheideStructuralInternalPair
public import LeanPool.GoldbergSeymour.ScheideSymmetricOriginalBoundaryAvoidance
public import LeanPool.GoldbergSeymour.ScheideSymmetricOriginalFreePath
public import LeanPool.GoldbergSeymour.ScheideSymmetricReplacementBoundaryAvoidance
public import LeanPool.GoldbergSeymour.ScheideSymmetricReplacementBoundaryConfiguration
public import LeanPool.GoldbergSeymour.ScheideSymmetricReplacementFreePath
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeUsedColors
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Scheide Symmetric Defective Internal

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem ScheideSymmetricDefectiveInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    (∃ f : E,
        phi f = some d.1 ∧
          G.ends f =
            s(C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1)) ∧
      ∃ f : E, phi f = some (C.gamma (D.gammaIndex d)) ∧ G.ends f = s(R.u1, R.u2) := by
  classical
  let X := TreeSequenceVertexSet T
  let ug0 := C.blockVertex (D.gammaIndex d) 0
  let ug1 := C.blockVertex (D.gammaIndex d) 1
  let Z := X \ {ug0, ug1}
  obtain ⟨beta, v, z, p, hvZ, hbetaMissing, hbetaFree, hbetaGamma, hp⟩ :=
    ScheideSymmetricOriginalFreePath G k e0 phi T C D d R
  have hOriginalAvoid :=
    ScheideSymmetricOriginalBoundaryAvoidance G k e0 phi T C D d R
      beta v z p (by simpa [X, Z, ug0, ug1] using hvZ)
      hbetaMissing hbetaFree hbetaGamma hp
  have hBoundaryAvoid :
    ∀ f : E, f ∈ BoundaryColorEdges G phi X d.1 →
    ∀ j : Fin 2, ¬ Incident G (C.blockVertex (D.gammaIndex d) j) f := by
    simpa only [X] using hOriginalAvoid.2
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hclosed : ColoredVertexSetClosed G phi X := by
    change ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)
    exact horder.2.2.2.2
  have hug0X : ug0 ∈ X := by
    change C.blockVertex (D.gammaIndex d) 0 ∈ TreeSequenceVertexSet T
    rw [← C.block_vertex_position (D.gammaIndex d) (0 : Fin 2)]
    simp [TreeSequenceVertexSet]
  have hdcard : 2 ≤ (BoundaryColorEdges G phi X d.1).card := by
    have hd := (Finset.mem_filter.mp d.2).2
    simpa only [DefectiveColor, X] using hd
  have hdnonempty : (BoundaryColorEdges G phi X d.1).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hdcard)
  obtain ⟨b, hb⟩ := hdnonempty
  have hbBoundary : b ∈ BoundaryEdges G X :=
    (Finset.mem_filter.mp hb).1
  have hbColor : phi b = some d.1 :=
    (Finset.mem_filter.mp hb).2
  have hdeltaNotMissing : d.1 ∉ MissingColors G phi ug0 :=
    hclosed hbBoundary hug0X hbColor
  have hdeltaPresent : d.1 ∈ PresentColors G phi ug0 := by
    simpa [MissingColors] using hdeltaNotMissing
  obtain ⟨fDelta, hfDeltaIncident, hfDeltaColor⟩ :
      ∃ f : E, Incident G ug0 f ∧ phi f = some d.1 := by
    simpa [PresentColors] using hdeltaPresent
  obtain ⟨wDelta, hfDeltaEnds⟩ := Sym2.mem_iff_exists.mp hfDeltaIncident
  have hwDeltaNe : wDelta ≠ ug0 := by
    intro heq
    exact G.loopless fDelta ug0 (by simpa [heq] using hfDeltaEnds)
  have hwDeltaX : wDelta ∈ X := by
    by_contra hw
    have hfBoundary : fDelta ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ug0, hug0X, wDelta, hw, hfDeltaEnds⟩
    have hfColorBoundary : fDelta ∈ BoundaryColorEdges G phi X d.1 := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      exact ⟨hfBoundary, hfDeltaColor⟩
    exact (hBoundaryAvoid fDelta hfColorBoundary (0 : Fin 2))
      (by simpa only [ug0] using hfDeltaIncident)
  have hwDeltaNotZ : wDelta ∉ Z := by
    intro hwZ
    have hnocross := ScheideDefectiveNoCross G k e0 phi T C D d
      fDelta hfDeltaColor
    apply hnocross
    refine ⟨ug0, ?_, hfDeltaIncident, wDelta, ?_, ?_⟩
    · simp [ug0]
    · simpa [X, Z, ug0, ug1] using hwZ
    · simp [Incident, hfDeltaEnds]
  have hwDeltaPair : wDelta ∈ ({ug0, ug1} : Finset V) := by
    by_contra hwPair
    exact hwDeltaNotZ (by simp [Z, hwDeltaX, hwPair])
  have hwDeltaEq : wDelta = ug1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwDeltaPair
    rcases hwDeltaPair with heq | heq
    · exact False.elim (hwDeltaNe heq)
    · exact heq
  have hfirst : ∃ f : E, phi f = some d.1 ∧
      G.ends f = s(C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1) := by
    refine ⟨fDelta, hfDeltaColor, ?_⟩
    simpa [ug0, ug1, hwDeltaEq] using hfDeltaEnds
  let gamma := C.gamma (D.gammaIndex d)
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let XD := TreeSequenceVertexSet R.replacementTree
  obtain ⟨betaD, vD, zD, pD, hvDZ, hbetaDMissing, hbetaDOldMissing,
      hbetaDFree, hbetaDDelta, hbetaDGamma, hpD⟩ :=
    ScheideSymmetricReplacementFreePath G k e0 phi T C D d R
  have hReplacementAvoid :=
    ScheideSymmetricReplacementBoundaryAvoidance G k e0 phi T C D d R
      betaD vD zD pD
      (by simpa [gamma, phiD, X, Z, ug0, ug1] using hvDZ)
      (by simpa [gamma, phiD] using hbetaDMissing)
      hbetaDOldMissing
      (by simpa [gamma, phiD] using hbetaDFree)
      hbetaDDelta (by simpa [gamma] using hbetaDGamma)
      (by simpa [gamma, phiD] using hpD)
  have hReplacementConfig :=
    ScheideSymmetricReplacementBoundaryConfiguration G k e0 phi T C D d R
  have hgammaDefective : gamma ∈ DefectiveColors G phiD XD := by
    simpa [gamma, phiD, XD, X, Z, ug0, ug1] using hReplacementConfig.1
  have hReplacementMaximum := ScheideReplacementMaximum G k e0 phi T C D d R
  have hReplacementOrder := ScheideGlobalMaximumOrder G k e0 phiD
    R.replacementTree (by simpa [gamma, phiD] using hReplacementMaximum.2.2)
  have hDClosed : ColoredVertexSetClosed G phiD XD := by
    change ColoredVertexSetClosed G phiD
      (TreeSequenceVertexSet R.replacementTree)
    exact hReplacementOrder.2.2.2.2
  have hu1XD : R.u1 ∈ XD := by
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices]
    simp
  have hgammaCard : 2 ≤ (BoundaryColorEdges G phiD XD gamma).card := by
    have hg := (Finset.mem_filter.mp hgammaDefective).2
    simpa only [DefectiveColor] using hg
  have hgammaNonempty : (BoundaryColorEdges G phiD XD gamma).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hgammaCard)
  obtain ⟨bD, hbD⟩ := hgammaNonempty
  have hbDBoundary : bD ∈ BoundaryEdges G XD :=
    (Finset.mem_filter.mp hbD).1
  have hbDColor : phiD bD = some gamma :=
    (Finset.mem_filter.mp hbD).2
  have hgammaNotMissing : gamma ∉ MissingColors G phiD R.u1 :=
    hDClosed hbDBoundary hu1XD hbDColor
  have hgammaPresent : gamma ∈ PresentColors G phiD R.u1 := by
    simpa [MissingColors] using hgammaNotMissing
  obtain ⟨fGamma, hfGammaIncident, hfGammaColor⟩ :
      ∃ f : E, Incident G R.u1 f ∧ phiD f = some gamma := by
    simpa [PresentColors] using hgammaPresent
  obtain ⟨wGamma, hfGammaEnds⟩ := Sym2.mem_iff_exists.mp hfGammaIncident
  have hwGammaNe : wGamma ≠ R.u1 := by
    intro heq
    exact G.loopless fGamma R.u1 (by simpa [heq] using hfGammaEnds)
  have hNoGammaBoundaryAtPair :
      ∀ f : E, f ∈ BoundaryColorEdges G phiD XD gamma →
        ¬ Incident G R.u1 f ∧ ¬ Incident G R.u2 f := by
    simpa only [gamma, phiD, XD] using hReplacementAvoid.2.1
  have hwGammaXD : wGamma ∈ XD := by
    by_contra hw
    have hfBoundary : fGamma ∈ BoundaryEdges G XD := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨R.u1, hu1XD, wGamma, hw, hfGammaEnds⟩
    have hfColorBoundary : fGamma ∈ BoundaryColorEdges G phiD XD gamma := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      exact ⟨hfBoundary, hfGammaColor⟩
    exact (hNoGammaBoundaryAtPair fGamma hfColorBoundary).1 hfGammaIncident
  have hwGammaNotZ : wGamma ∉ Z := by
    intro hwZ
    have hnocross := hReplacementAvoid.2.2 fGamma
      (by simpa [gamma, phiD] using hfGammaColor)
      (Or.inl hfGammaIncident) wGamma
      (by simpa [X, Z, ug0, ug1] using hwZ)
    exact hnocross (by simp [Incident, hfGammaEnds])
  have hwGammaInUnion : wGamma ∈ Z ∪ {R.u1, R.u2} := by
    have hw := hwGammaXD
    rw [show XD = TreeSequenceVertexSet R.replacementTree by rfl,
      R.replacement_vertices] at hw
    simpa [X, Z, ug0, ug1] using hw
  have hwGammaPair : wGamma ∈ ({R.u1, R.u2} : Finset V) := by
    simpa [hwGammaNotZ] using hwGammaInUnion
  have hwGammaEq : wGamma = R.u2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwGammaPair
    rcases hwGammaPair with heq | heq
    · exact False.elim (hwGammaNe heq)
    · exact heq
  have hfGammaOriginal : phi fGamma = some gamma := by
    have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R
      fGamma (Or.inl hfGammaIncident)
    change TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
      (Sum.inl (D.v0 d)) fGamma =
        some (C.gamma (D.gammaIndex d)) at hfGammaColor
    rw [hfixed] at hfGammaColor
    simpa [gamma] using hfGammaColor
  refine ⟨hfirst, fGamma, ?_, ?_⟩
  · simpa [gamma] using hfGammaOriginal
  · simpa [hwGammaEq] using hfGammaEnds

end GoldbergSeymour

end
