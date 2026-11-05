/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.Elementary
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainDepartureReturn
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPathExists
public import LeanPool.GoldbergSeymour.ScheideDepartureReturn
public import LeanPool.GoldbergSeymour.ScheideExitNoFree
public import LeanPool.GoldbergSeymour.ScheideExitVertex
public import LeanPool.GoldbergSeymour.ScheideExitVertices
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumBoundaryFacts
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGraphHeight
public import LeanPool.GoldbergSeymour.TashkinovOrder
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeUsedColors
public import LeanPool.GoldbergSeymour.CriticalGraphElementaryWitness

/-!
# Scheide Large Height Full Trunk

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideLargeHeightFullTrunk {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hheight : ScheideGraphHeight G = TashkinovOrder G) :
    Elementary G := by
  classical
  let : DecidableEq V := Classical.decEq V
  have hcard : (TreeSequenceVertexSet T).card = T.length + 1 := by
    unfold TreeSequenceVertexSet
    rw [Finset.card_image_iff.mpr (by
      intro a ha b hb hab
      exact T.vertex_injective hab)]
    simp
  have horder := ScheideGlobalMaximumOrder G k e0 phi T N.global
  have hheight : N.height = T.length + 1 := by
    calc
      N.height = ScheideGraphHeight G := hbalanced.1
      _ = TashkinovOrder G := hheight
      _ = (TreeSequenceVertexSet T).card := horder.1
      _ = T.length + 1 := hcard
  have hheight_eq : N.height = T.length + 1 := hheight
  have htrunk : ∀ j : Fin T.length, 1 ≤ j.val →
      ∃ c : Fin k, phi (T.edge j) = some c ∧ (c = N.alpha ∨ c = N.beta) := by
    intro j hj
    have hjh : j.val + 2 ≤ N.height := by rw [hheight_eq]; omega
    have hs := (N.closingPath_edges (T.edge j)).2
      (Or.inr ⟨j, hj, hjh, rfl⟩)
    have he := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hs
    rcases he with ⟨n, hnedge, hn⟩
    have hnpos : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := by omega
      subst n
      have hz := N.closingPath.getVert_zero
      rw [hz] at hnedge
      simp at hnedge
    have hnlt : n < N.closingPath.length := by
      by_contra hnlt
      have hlen := N.closingPath_length
      rw [hheight_eq] at hlen
      have hh := N.height_lower
      have hstart := N.closingPath.getVert_of_length_le (i := n) (by omega)
      rw [hnedge] at hstart
      simp at hstart
    have hn' := N.closingPath.adj_getVert_succ (i := n - 1) (by omega)
    have hn'' : n - 1 + 1 = n := by omega
    have hnedge' : N.closingPath.getVert (n - 1 + 1) = Sum.inr (T.edge j) := by
      simpa [hn''] using hnedge
    rw [hnedge'] at hn'
    cases hx : N.closingPath.getVert (n - 1) with
    | inl v =>
      rw [hx] at hn'
      simp only [TwoColorIncidenceGraph] at hn'
      rcases hn' with ⟨_, h | h⟩
      · exact ⟨N.alpha, h, Or.inl rfl⟩
      · exact ⟨N.beta, h, Or.inr rfl⟩
    | inr e =>
      rw [hx] at hn'
      simp [TwoColorIncidenceGraph] at hn'
  have hdef : DefectiveColors G phi (TreeSequenceVertexSet T) = ∅ := by
    by_contra hnon
    have hmem := Finset.nonempty_iff_ne_empty.mpr hnon
    rcases hmem with ⟨delta, hdelta⟩
    have hfree : ∀ v : V, v ∈ TreeSequenceVertexSet T →
        ∃ gamma, gamma ∈ MissingColors G phi v ∧
          gamma ∈ TreeFreeColors phi T := by
      intro v hv
      have hmissing : 1 ≤ (MissingColors G phi v).card := by
        have hm := ScheideGlobalMaximumMissingCounts G k e0 phi T N.global v hv
        by_cases hi : Incident G v e0
        · have hm' := (hm.1 hi).2
          omega
        · exact (hm.2 hi).2
      have hpos : 0 < (MissingColors G phi v).card := by omega
      obtain ⟨gamma, hgamma⟩ := Finset.card_pos.mp hpos
      let vzero : V := T.vertex ⟨0, T.length.succ_pos⟩
      let vone : V := T.vertex ⟨1, by omega⟩
      have hvzero : vzero ∈ TreeSequenceVertexSet T := by
        simp [TreeSequenceVertexSet, vzero]
      have hvone : vone ∈ TreeSequenceVertexSet T := by
        simp [TreeSequenceVertexSet, vone]
      have hne : vzero ≠ vone := by
        intro heq
        have hi := T.vertex_injective heq
        simp [] at hi
      have hinczero : Incident G vzero e0 := by
        unfold Incident
        rw [← T.first_edge]
        obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
        have iz : i = ⟨0, by omega⟩ := Fin.eq_zero i
        subst i
        rw [hi]
        simp only [Sym2.mem_iff]
        exact Or.inr rfl
      have hincone : Incident G vone e0 := by
        unfold Incident
        rw [← T.first_edge]
        obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
        have iz : i = ⟨0, by omega⟩ := Fin.eq_zero i
        subst i
        rw [hi]
        simp only [Sym2.mem_iff]
        exact Or.inl rfl
      have hgamma' : ∃ c, c ∈ MissingColors G phi v ∧
          c ≠ N.alpha ∧ c ≠ N.beta := by
        by_cases hv0 : v = vzero
        · subst v
          have hm := (ScheideGlobalMaximumMissingCounts G k e0 phi T N.global
            vzero hvzero).1 hinczero
          obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne hm.2 N.alpha
          have hcb : c ≠ N.beta := by
            intro hce
            have he := horder.2.2.2.1 hvzero hvone hne
            exact Finset.disjoint_left.mp he hc (by simpa [hce, vzero] using N.beta_missing)
          exact ⟨c, hc, hca, hcb⟩
        · by_cases hv1 : v = vone
          · have hm := (ScheideGlobalMaximumMissingCounts G k e0 phi T N.global
              vone hvone).1 hincone
            obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_ne hm.2 N.beta
            have hca : c ≠ N.alpha := by
              intro hce
              have he := horder.2.2.2.1 hvone hvzero hne.symm
              exact Finset.disjoint_left.mp he hc (by simpa [hce, vzero] using N.alpha_missing)
            exact ⟨c, by simpa [hv1] using hc, hca, hcb⟩
          · have hca : gamma ≠ N.alpha := by
              intro h
              exact Finset.disjoint_left.mp
                (horder.2.2.2.1 hv hvzero hv0) hgamma
                (by simpa [h, vzero] using N.alpha_missing)
            have hcb : gamma ≠ N.beta := by
              intro h
              exact Finset.disjoint_left.mp
                (horder.2.2.2.1 hv hvone hv1) hgamma
                (by simpa [h, vone] using N.beta_missing)
            exact ⟨gamma, hgamma, hca, hcb⟩
      rcases hgamma' with ⟨gamma, hgamma, hnotzero, hnotone⟩
      have htm : gamma ∈ TreeMissingColors phi T := by
        unfold TreeMissingColors
        simp only [Finset.mem_biUnion]
        exact ⟨v, hv, hgamma⟩
      have htu : gamma ∉ TreeUsedColors phi T := by
        intro hu
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        rcases hu with ⟨j, hj, he⟩
        obtain ⟨c, hc, hcb⟩ := htrunk j hj
        have heq := Option.some.inj (he.symm.trans hc)
        rcases hcb with rfl | rfl
        · exact hnotzero heq
        · exact hnotone heq
      refine ⟨gamma, hgamma, ?_⟩
      change gamma ∈ TreeMissingColors phi T \ TreeUsedColors phi T
      exact Finset.mem_sdiff.mpr ⟨htm, htu⟩
    let vzero : V := T.vertex ⟨0, T.length.succ_pos⟩
    have hvzero : vzero ∈ TreeSequenceVertexSet T := by
      simp [TreeSequenceVertexSet, vzero]
    obtain ⟨gamma, hgamma, hfreegamma⟩ := hfree vzero hvzero
    obtain ⟨z, p, hp⟩ := ScheideDefectiveChainPathExists G k e0 phi T N.global
      delta gamma hdelta hfreegamma vzero hvzero hgamma
    obtain ⟨i1, i2, v1, v2, hreturn⟩ :=
      ScheideDefectiveChainDepartureReturn G k e0 phi T N.global delta gamma
        hdelta hfreegamma vzero hvzero hgamma z p hp
    rcases hreturn with ⟨hpathret, hi1, hvout, hbefore, hlt, hi2, hv2, hafter⟩
    have hexit : ScheideExitVertex T phi v2 := by
      exact ⟨vzero, gamma, delta, hvzero, hgamma, hdelta, z, p, hpathret,
        ⟨i2, hi2, hv2, hafter⟩⟩
    have hmemexit : v2 ∈ ScheideExitVertices T phi := by
      simp [ScheideExitVertices, hexit]
    have hdis := ScheideExitNoFree G k e0 phi T N.global v2 hmemexit
    obtain ⟨gamma2, hgamma2, hfree2⟩ := hfree v2 hv2
    exact (Finset.disjoint_left.mp hdis) hgamma2 hfree2
  have hstrong := (ScheideGlobalMaximumBoundaryFacts G k e0 phi T N.global).1 hdef
  have hends : ∀ v : V, v ∈ G.ends e0 → v ∈ TreeSequenceVertexSet T := by
    intro v hv
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    have iz : i = ⟨0, by omega⟩ := Fin.eq_zero i
    subst i
    rw [← T.first_edge] at hv
    rw [hi] at hv
    simp only [Sym2.mem_iff] at hv
    rcases hv with hv | hv
    · subst v
      simp [TreeSequenceVertexSet]
    · apply Finset.mem_image.mpr
      exact ⟨_, Finset.mem_univ _, hv.symm⟩
  have hw : ∃ (e : E) (p : PartialEdgeColoring E k) (X : Finset V),
      IsProperEdgeColoring G p ∧ IsOneEdgeUncolored p e ∧
        (∀ v, v ∈ G.ends e → v ∈ X) ∧
        ColoredVertexSetElementary G p X ∧
        ColoredVertexSetStronglyClosed G p X :=
    ⟨e0, phi, TreeSequenceVertexSet T, N.global.1.2.2.2.1,
      N.global.1.2.2.2.2, hends, horder.2.2.2.1, hstrong⟩
  have hc := (egraph2 G k N.global.1.1 N.global.1.2.1 N.global.1.2.2.1 hnoisolated).2.2.2 hw
  exact (egraph2 G k N.global.1.1 N.global.1.2.1 N.global.1.2.2.1 hnoisolated).1.mpr
    ((egraph2 G k N.global.1.1 N.global.1.2.1 N.global.1.2.2.1 hnoisolated).2.1.mpr hc)

end GoldbergSeymour

end
