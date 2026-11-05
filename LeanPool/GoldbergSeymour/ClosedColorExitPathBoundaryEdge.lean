/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeExitPath

/-!
# Closed Color Exit Path Boundary Edge

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

lemma ClosedColorExitPathBoundaryEdge {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (a b : Fin k)
    (hclosed : TreeColorSetClosed G phi T {a})
    (u v : V)
    (P : (TwoColorIncidenceGraph G phi a b).Walk
      (Sum.inl u) (Sum.inl v))
    (hP : TreeExitPath T phi a b u v P) :
    ∃ f : E,
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b ∧
      Incident G v f ∧ Sum.inr f ∈ P.support := by
  classical
  rcases hP with ⟨_, _, huX, hvX, _, honly⟩
  let H := TwoColorIncidenceGraph G phi a b
  let X := TreeSequenceVertexSet T
  let S : Set (Sum V E) := {y | match y with
    | Sum.inl q => q ∈ X
    | Sum.inr f => ∀ q, Incident G q f → q ∈ X}
  have hSv : Sum.inl v ∈ S := by
    simpa [S, X] using hvX
  have hSu : Sum.inl u ∉ S := by
    simpa [S, X] using huX
  obtain ⟨d, hd, hds, hdt⟩ :=
    P.reverse.exists_boundary_dart S hSv hSu
  have hadj := d.adj
  have hdmem : d.toProd.1 ∈ P.reverse.support :=
    P.reverse.dart_fst_mem_support_of_mem_darts hd
  have hdtmem : d.toProd.2 ∈ P.reverse.support :=
    P.reverse.dart_snd_mem_support_of_mem_darts hd
  have hfirst : ∃ q : V, d.toProd.1 = Sum.inl q ∧ q ∈ X := by
    cases h : d.toProd.1 with
    | inl q =>
        rw [h] at hds
        exact ⟨q, rfl, by simpa [S] using hds⟩
    | inr f =>
        exfalso
        cases h2 : d.toProd.2 with
        | inl r =>
            rw [h, h2] at hadj
            change Incident G r f ∧
              (phi f = some a ∨ phi f = some b) at hadj
            rw [h] at hds
            have hall : ∀ q, Incident G q f → q ∈ X := by
              simpa [S] using hds
            have hrnot : r ∉ X := by
              intro hr
              apply hdt
              simpa [S, h2] using hr
            exact hrnot (hall r hadj.1)
        | inr e =>
            rw [h, h2] at hadj
            exact hadj.elim
  obtain ⟨q, hq, hqX⟩ := hfirst
  have hsecond : ∃ f : E, d.toProd.2 = Sum.inr f := by
    cases h : d.toProd.2 with
    | inl r =>
        rw [hq, h] at hadj
        exact False.elim hadj
    | inr f => exact ⟨f, rfl⟩
  obtain ⟨f, hf⟩ := hsecond
  have hfadj : H.Adj (Sum.inl q) (Sum.inr f) := by
    rw [hq, hf] at hadj
    exact hadj
  have hfdata : Incident G q f ∧
      (phi f = some a ∨ phi f = some b) := by
    simpa [H, TwoColorIncidenceGraph] using hfadj
  have hnotall : ¬ ∀ r, Incident G r f → r ∈ X := by
    intro hall
    apply hdt
    simpa [S, hf, hall]
  obtain ⟨r, hrf, hrX⟩ : ∃ r, Incident G r f ∧ r ∉ X := by
    push Not at hnotall
    exact hnotall
  have hqr : q ≠ r := by
    intro h
    exact hrX (h ▸ hqX)
  have hend : G.ends f = s(q, r) :=
    (Sym2.mem_and_mem_iff hqr).mp ⟨hfdata.1, hrf⟩
  have hfb : f ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q, hqX, r, hrX, hend⟩
  have hfcolor : phi f = some b := by
    rcases hfdata.2 with hfa | hfbeta
    · have hfalpha : f ∈ BoundaryColorEdges G phi X a := by
        simp [BoundaryColorEdges, hfb, hfa]
      have hempty := hclosed a (by simp)
      rw [hempty] at hfalpha
      simp at hfalpha
    · exact hfbeta
  have hqP : Sum.inl q ∈ P.support := by
    have hqrev : Sum.inl q ∈ P.reverse.support := by
      rw [← hq]
      exact hdmem
    simpa [SimpleGraph.Walk.support_reverse] using hqrev
  have hqv : q = v := (honly q (by simpa [X] using hqX)).mp hqP
  have hfP : Sum.inr f ∈ P.support := by
    have hfrev : Sum.inr f ∈ P.reverse.support := by
      rw [← hf]
      exact hdtmem
    simpa [SimpleGraph.Walk.support_reverse] using hfrev
  subst q
  exact ⟨f, by simpa [X, BoundaryColorEdges] using
      (show f ∈ BoundaryColorEdges G phi X b by
        simp [BoundaryColorEdges, hfb, hfcolor]), hfdata.1, hfP⟩

end GoldbergSeymour

end
