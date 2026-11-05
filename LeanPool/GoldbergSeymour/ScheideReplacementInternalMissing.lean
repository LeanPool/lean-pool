/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReplacementMaximum
public import LeanPool.GoldbergSeymour.ScheideReplacementPairFixed

/-!
# Scheide Replacement Internal Missing

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem ScheideReplacementInternalMissing {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ alpha : Fin k, alpha ≠ C.gamma (D.gammaIndex d) → (
    ∃ z ∈ TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}, alpha ∈
        MissingColors G phi z) →
    ∃ f : E, phi f = some alpha ∧ G.ends f = s(R.u1, R.u2) := by
  classical
  intro alpha halpha hdata
  rcases hdata with ⟨z, hz, hzm⟩
  let phiD := TwoColorComponentSwap G phi
    (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
  have hmax := ScheideReplacementMaximum G k e0 phi T C D d R
  dsimp [phiD] at hmax ⊢
  have horder := ScheideGlobalMaximumOrder G k e0 phiD R.replacementTree hmax.2.2
  have hproper : IsProperEdgeColoring G phiD := hmax.1
  have helem : ColoredVertexSetElementary G phiD
      (TreeSequenceVertexSet R.replacementTree) := horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phiD
      (TreeSequenceVertexSet R.replacementTree) := horder.2.2.2.2
  have hold := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have holdclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    hold.2.2.2.2
  have hdelta_ne : alpha ≠ d.1 := by
    intro heq
    have hd : 2 ≤ (BoundaryColorEdges G phi (TreeSequenceVertexSet T) d.1).card :=
      (Finset.mem_filter.mp d.2).2
    have hpos : (BoundaryColorEdges G phi (TreeSequenceVertexSet T) d.1).Nonempty :=
      Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hd)
    rcases hpos with ⟨f, hf⟩
    have hparts := Finset.mem_filter.mp hf
    have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := hparts.1
    have hfc : phi f = some d.1 := hparts.2
    have hn := holdclosed hfb (Finset.mem_sdiff.mp hz).1 hfc
    exact hn (heq ▸ hzm)
  have hsw := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  dsimp at hsw
  have hzmD : alpha ∈ MissingColors G phiD z := by
    have hn : alpha ∉ PresentColors G phiD z := by
      intro hp
      rcases (show ∃ e, Incident G z e ∧ phiD e = some alpha by
        simpa [PresentColors] using hp) with ⟨e, he, hc⟩
      have ho : phi e = some alpha := by
        by_cases hk : Sum.inr e ∈
            TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
              (Sum.inl (D.v0 d))
        · rw [show phiD e =
              (if phi e = some (C.gamma (D.gammaIndex d)) then some d.1
                else if phi e = some d.1 then some (C.gamma (D.gammaIndex d))
                else phi e) by simp [phiD, TwoColorComponentSwap, hk]] at hc
          by_cases hg : phi e = some (C.gamma (D.gammaIndex d))
          · simp [hg] at hc
            exact False.elim (hdelta_ne hc.symm)
          · by_cases hd : phi e = some d.1
            · by_cases hdg : d.1 = C.gamma (D.gammaIndex d)
              · simp [hd, hdg] at hc
                exact False.elim (halpha hc.symm)
              · simp [hd, hdg] at hc
                exact False.elim (halpha hc.symm)
            · simpa [hg, hd] using hc
        · simpa [phiD, TwoColorComponentSwap, hk] using hc
      exact (Finset.mem_sdiff.mp hzm).2 (by
        simpa [PresentColors] using ⟨e, he, ho⟩)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
  have hzrep : z ∈ TreeSequenceVertexSet R.replacementTree := by
    rw [R.replacement_vertices]
    exact Finset.mem_union.mpr (Or.inl hz)
  have hne1 : z ≠ R.u1 := by
    intro e
    subst e
    exact R.u1_outside (Finset.mem_sdiff.mp hz).1
  have hne2 : z ≠ R.u2 := by
    intro e
    subst e
    exact R.u2_outside (Finset.mem_sdiff.mp hz).1
  have hp1 : alpha ∈ PresentColors G phiD R.u1 := by
    have hu : R.u1 ∈ TreeSequenceVertexSet R.replacementTree := by
      rw [R.replacement_vertices]
      simp [R.u1_outside]
    have hdj := helem (u := z) hzrep (v := R.u1) hu hne1
    have hn : alpha ∉ MissingColors G phiD R.u1 := by
      intro hu
      exact Finset.disjoint_left.mp hdj hzmD hu
    simpa [MissingColors] using hn
  rcases (show ∃ e, Incident G R.u1 e ∧ phiD e = some alpha by
    simpa [PresentColors] using hp1) with ⟨f, hf1, hfc⟩
  have hfu2 : Incident G R.u2 f := by
    obtain ⟨w, hends⟩ := Sym2.mem_iff_exists.mp hf1
    have hwrep : w ∈ TreeSequenceVertexSet R.replacementTree := by
      by_contra hwout
      have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet R.replacementTree) := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        have hu : R.u1 ∈ TreeSequenceVertexSet R.replacementTree := by
          rw [R.replacement_vertices]
          simp [R.u1_outside]
        exact ⟨R.u1, hu, w, hwout, hends⟩
      exact hclosed hfb hzrep hfc hzmD
    rw [R.replacement_vertices] at hwrep
    rcases Finset.mem_union.mp hwrep with hwz | hwu
    · have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w, (Finset.mem_sdiff.mp hwz).1, R.u1, R.u1_outside,
          by simpa [Sym2.eq_swap] using hends⟩
      have horig : phi f = some alpha := by
        have hi := ScheideReplacementPairFixed G k e0 phi T C D d R f (Or.inl hf1)
        exact hi.symm.trans hfc
      have hn := holdclosed hfb (Finset.mem_sdiff.mp hz).1 horig
      exact False.elim (hn hzm)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hwu
      rcases hwu with rfl | rfl
      · exact False.elim (G.loopless f R.u1 (by simp [hends]))
      · change R.u2 ∈ G.ends f
        rw [hends]
        exact Sym2.mem_mk_right R.u1 R.u2
  have hu1u2 : R.u1 ≠ R.u2 := by
    intro h
    have hi := R.replacementTree.vertex_injective
      (R.replacement_last_vertices.1.trans
        (h.trans R.replacement_last_vertices.2.symm))
    have hv : T.length - 1 = T.length := by
      simpa using congrArg Fin.val hi
    have ht := T.positive
    omega
  have hfixed := ScheideReplacementPairFixed G k e0 phi T C D d R f (Or.inl hf1)
  exact ⟨f, hfixed.symm.trans hfc, by
    exact (Sym2.mem_and_mem_iff hu1u2).mp ⟨hf1, hfu2⟩⟩

end GoldbergSeymour

end
