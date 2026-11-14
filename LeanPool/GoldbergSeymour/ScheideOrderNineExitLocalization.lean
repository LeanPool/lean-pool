/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ScheideExitNoFree
public import LeanPool.GoldbergSeymour.ScheideExitVertices
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts

/-!
# Scheide Order Nine Exit Localization

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideOrderNineExitLocalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (_ : BalancedGlobalMaximumTriple N)
    (hlength : T.length = 8) (hheight : N.height = 5)
    (gamma : Fin 2 → Fin k)
    (_ : Function.Injective gamma)
    (hblockColor : ∀ (i : Fin 2) (j : Fin 2),
      phi (T.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
        some (gamma i))
    (_ : ∀ i : Fin 2, ∃ q : Fin 5,
      gamma i ∈ MissingColors G phi (T.vertex ⟨q.val, by omega⟩))
    (_ : ∀ i : Fin 4, 1 ≤ i.val →
      ∀ c : Fin k, phi (T.edge ⟨i.val, by omega⟩) = some c →
        ∀ r : Fin 2, c ≠ gamma r) :
    ∀ v ∈ ScheideExitVertices T phi,
    ∃ i : Fin 2,
    gamma i ∈ MissingColors G phi v := by
  classical
  let : DecidableEq V := Classical.decEq V
  have horder := ScheideGlobalMaximumOrder G k e0 phi T N.global
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.1
  let y0 : V := T.vertex ⟨0, Nat.zero_lt_succ T.length⟩
  let y1 : V := T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩
  have hy0T : y0 ∈ TreeSequenceVertexSet T := by
    simp [y0, TreeSequenceVertexSet]
  have hy1T : y1 ∈ TreeSequenceVertexSet T := by
    simp [y1, TreeSequenceVertexSet]
  have hy01 : y0 ≠ y1 := by
    intro h
    have hi := T.vertex_injective h
    simp [] at hi
  have he0ends : G.ends e0 = s(y1, y0) := by
    rw [← T.first_edge]
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    have hiz : i = ⟨0, by omega⟩ := Fin.eq_zero i
    subst i
    rw [hi]
    congr 2
  have hy0inc : Incident G y0 e0 := by
    unfold Incident
    rw [he0ends]
    simp [Sym2.mem_iff]
  have hy1inc : Incident G y1 e0 := by
    unfold Incident
    rw [he0ends]
    simp [Sym2.mem_iff]
  have incident_cases {v : V} (hv : Incident G v e0) : v = y0 ∨ v = y1 := by
    unfold Incident at hv
    rw [he0ends, Sym2.mem_iff] at hv
    exact hv.symm
  have edge_color_of_closing_support (f : E)
      (hf : Sum.inr f ∈ N.closingPath.support) :
      phi f = some N.alpha ∨ phi f = some N.beta := by
    exact TwoColorIncidenceGraph.edge_colors_of_mem_walk_support N.closingPath hf
  have hnormalColor : ∀ j : Fin T.length, 1 ≤ j.val → j.val < 4 →
      phi (T.edge j) = some N.alpha ∨ phi (T.edge j) = some N.beta := by
    intro j hjpos hjlt
    apply edge_color_of_closing_support
    apply (N.closingPath_edges (T.edge j)).2
    exact Or.inr ⟨j, hjpos, by omega, rfl⟩
  have hused : ∀ c : Fin k, c ∈ TreeUsedColors phi T →
      c = N.alpha ∨ c = N.beta ∨ ∃ i : Fin 2, c = gamma i := by
    intro c hc
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨j, hjpos, hjcolor⟩ := hc
    have hjlt : j.val < 8 := by
      rw [← hlength]
      exact j.isLt
    by_cases hjbase : j.val < 4
    · rcases hnormalColor j hjpos hjbase with ha | hb
      · exact Or.inl (Option.some.inj (hjcolor.symm.trans ha))
      · exact Or.inr (Or.inl (Option.some.inj (hjcolor.symm.trans hb)))
    · have hvals : j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 := by
        omega
      rcases hvals with hval | hval | hval | hval
      · right; right
        have hjEq : j = ⟨4, by omega⟩ := Fin.ext hval
        rw [hjEq] at hjcolor
        refine ⟨⟨0, by omega⟩, ?_⟩
        exact Option.some.inj (hjcolor.symm.trans (by
          simpa using hblockColor ⟨0, by omega⟩ ⟨0, by omega⟩))
      · right; right
        have hjEq : j = ⟨5, by omega⟩ := Fin.ext hval
        rw [hjEq] at hjcolor
        refine ⟨⟨0, by omega⟩, ?_⟩
        exact Option.some.inj (hjcolor.symm.trans (by
          simpa using hblockColor ⟨0, by omega⟩ ⟨1, by omega⟩))
      · right; right
        have hjEq : j = ⟨6, by omega⟩ := Fin.ext hval
        rw [hjEq] at hjcolor
        refine ⟨⟨1, by omega⟩, ?_⟩
        exact Option.some.inj (hjcolor.symm.trans (by
          simpa using hblockColor ⟨1, by omega⟩ ⟨0, by omega⟩))
      · right; right
        have hjEq : j = ⟨7, by omega⟩ := Fin.ext hval
        rw [hjEq] at hjcolor
        refine ⟨⟨1, by omega⟩, ?_⟩
        exact Option.some.inj (hjcolor.symm.trans (by
          simpa using hblockColor ⟨1, by omega⟩ ⟨1, by omega⟩))
  intro v hvExit
  have hExitPred : ScheideExitVertex T phi v := by
    simpa [ScheideExitVertices] using hvExit
  obtain ⟨u, gamma', delta, hu, hgammaMissing, hdelta, z, p, hp,
      i, hi, hvT, hafter⟩ := hExitPred
  by_contra hgoal
  push Not at hgoal
  have hcounts := ScheideGlobalMaximumMissingCounts G k e0 phi T N.global v hvT
  have find_free (hc : Fin k) (hcMissing : hc ∈ MissingColors G phi v)
      (hcAlpha : hc ≠ N.alpha) (hcBeta : hc ≠ N.beta) : False := by
    have hcGamma : ∀ r : Fin 2, hc ≠ gamma r := by
      intro r hcr
      apply hgoal r
      simpa [← hcr] using hcMissing
    have hcNotUsed : hc ∉ TreeUsedColors phi T := by
      intro hcUsed
      rcases hused hc hcUsed with h | h | ⟨r, h⟩
      · exact hcAlpha h
      · exact hcBeta h
      · exact hcGamma r h
    have hcTreeMissing : hc ∈ TreeMissingColors phi T := by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨v, hvT, hcMissing⟩
    have hcFree : hc ∈ TreeFreeColors phi T := by
      exact Finset.mem_sdiff.mpr ⟨hcTreeMissing, hcNotUsed⟩
    have hnoFree := ScheideExitNoFree G k e0 phi T N.global v hvExit
    exact (Finset.disjoint_left.mp hnoFree) hcMissing hcFree
  by_cases hvInc : Incident G v e0
  · rcases incident_cases hvInc with rfl | rfl
    · obtain ⟨c, hc, hcAlpha⟩ :=
        Finset.exists_mem_ne ((hcounts.1 hy0inc).2) N.alpha
      have hcBeta : c ≠ N.beta := by
        intro hcb
        have hd := helem hy0T hy1T hy01
        exact (Finset.disjoint_left.mp hd) hc (by
          simpa [hcb, y1] using N.beta_missing)
      exact find_free c hc hcAlpha hcBeta
    · obtain ⟨c, hc, hcBeta⟩ :=
        Finset.exists_mem_ne ((hcounts.1 hy1inc).2) N.beta
      have hcAlpha : c ≠ N.alpha := by
        intro hca
        have hd := helem hy1T hy0T hy01.symm
        exact (Finset.disjoint_left.mp hd) hc (by
          simpa [hca, y0] using N.alpha_missing)
      exact find_free c hc hcAlpha hcBeta
  · have hnonempty : (MissingColors G phi v).Nonempty :=
      Finset.card_pos.mp (by have := (hcounts.2 hvInc).2; omega)
    obtain ⟨c, hc⟩ := hnonempty
    have hv0 : v ≠ y0 := by
      intro h
      subst v
      exact hvInc hy0inc
    have hv1 : v ≠ y1 := by
      intro h
      subst v
      exact hvInc hy1inc
    have hcAlpha : c ≠ N.alpha := by
      intro hca
      have hd := helem hvT hy0T hv0
      exact (Finset.disjoint_left.mp hd) hc (by
        simpa [hca, y0] using N.alpha_missing)
    have hcBeta : c ≠ N.beta := by
      intro hcb
      have hd := helem hvT hy1T hv1
      exact (Finset.disjoint_left.mp hd) hc (by
        simpa [hcb, y1] using N.beta_missing)
    exact find_free c hc hcAlpha hcBeta

end GoldbergSeymour

end
