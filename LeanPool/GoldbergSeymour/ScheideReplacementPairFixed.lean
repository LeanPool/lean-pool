/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideDefectiveTailExternal

/-!
# Scheide Replacement Pair Fixed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideReplacementPairFixed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    ∀ f : E, (Incident G R.u1 f ∨ Incident G R.u2 f) →
      TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)) f = phi f := by
  classical
  intro f hf
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have no_u1 : Sum.inl R.u1 ∉
      TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)) := by
    intro hu
    have hf1u : Incident G R.u1 R.f1 := by
      change R.u1 ∈ G.ends R.f1
      rw [R.f1_ends]
      simp []
    have hadj₁ : (TwoColorIncidenceGraph G phi
        (C.gamma (D.gammaIndex d)) d.1).Adj
        (Sum.inl R.u1) (Sum.inr R.f1) := by
      simp [TwoColorIncidenceGraph, hf1u, R.f1_color]
    have hf1c : Sum.inr R.f1 ∈
        TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d)) := by
      change (TwoColorIncidenceGraph G phi
        (C.gamma (D.gammaIndex d)) d.1).connectedComponentMk
          (Sum.inr R.f1) =
        (TwoColorIncidenceGraph G phi
          (C.gamma (D.gammaIndex d)) d.1).connectedComponentMk
          (Sum.inl (D.v0 d))
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj₁).symm.trans hu
    have hf1v : Incident G R.v1 R.f1 := by
      change R.v1 ∈ G.ends R.f1
      rw [R.f1_ends]
      simp []
    have hadj₂ : (TwoColorIncidenceGraph G phi
        (C.gamma (D.gammaIndex d)) d.1).Adj
        (Sum.inr R.f1) (Sum.inl R.v1) := by
      simp [TwoColorIncidenceGraph, hf1v, R.f1_color]
    have hv1c : Sum.inl R.v1 ∈
        TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d)) := by
      change (TwoColorIncidenceGraph G phi
        (C.gamma (D.gammaIndex d)) d.1).connectedComponentMk
          (Sum.inl R.v1) =
        (TwoColorIncidenceGraph G phi
          (C.gamma (D.gammaIndex d)) d.1).connectedComponentMk
          (Sum.inl (D.v0 d))
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj₂).symm.trans hf1c
    have hv1tree : R.v1 ∈ TreeSequenceVertexSet T := by
      have hrem : R.v1 ∈ TreeSequenceVertexSet T ∧
          R.v1 ≠ C.blockVertex (D.gammaIndex d) 0 ∧
          R.v1 ≠ C.blockVertex (D.gammaIndex d) 1 := by
        simpa using R.v1_in_remainder
      exact hrem.1
    have hv1 : R.v1 = D.v0 d :=
      ScheideDefectiveTailExternal G k e0 phi T C D d R.v1 hv1tree hv1c
    have hf0v : Incident G (D.v0 d) (D.f0 d) := by
      change D.v0 d ∈ G.ends (D.f0 d)
      rw [D.f0_ends]
      simp []
    have hf0c : phi (D.f0 d) = some d.1 := D.f0_color d
    have hadj : AdjacentEdges G (D.f0 d) R.f1 :=
      ⟨D.v0 d, hf0v, hv1 ▸ hf1v⟩
    have hbad := hproper R.f0_ne_f1 hadj hf0c
    exact hbad R.f1_color
  have no_u2 : Sum.inl R.u2 ∉
      TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
        (Sum.inl (D.v0 d)) := by
    intro hu
    have hf2u : Incident G R.u2 R.f2 := by
      change R.u2 ∈ G.ends R.f2
      rw [R.f2_ends]
      simp []
    have hadj₁ : (TwoColorIncidenceGraph G phi
        (C.gamma (D.gammaIndex d)) d.1).Adj
        (Sum.inl R.u2) (Sum.inr R.f2) := by
      simp [TwoColorIncidenceGraph, hf2u, R.f2_color]
    have hf2c : Sum.inr R.f2 ∈
        TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d)) := by
      change (TwoColorIncidenceGraph G phi
        (C.gamma (D.gammaIndex d)) d.1).connectedComponentMk
          (Sum.inr R.f2) =
        (TwoColorIncidenceGraph G phi
          (C.gamma (D.gammaIndex d)) d.1).connectedComponentMk
          (Sum.inl (D.v0 d))
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj₁).symm.trans hu
    have hf2v : Incident G R.v2 R.f2 := by
      change R.v2 ∈ G.ends R.f2
      rw [R.f2_ends]
      simp []
    have hadj₂ : (TwoColorIncidenceGraph G phi
        (C.gamma (D.gammaIndex d)) d.1).Adj
        (Sum.inr R.f2) (Sum.inl R.v2) := by
      simp [TwoColorIncidenceGraph, hf2v, R.f2_color]
    have hv2c : Sum.inl R.v2 ∈
        TwoColorComponent G phi (C.gamma (D.gammaIndex d)) d.1
          (Sum.inl (D.v0 d)) := by
      change (TwoColorIncidenceGraph G phi
        (C.gamma (D.gammaIndex d)) d.1).connectedComponentMk
          (Sum.inl R.v2) =
        (TwoColorIncidenceGraph G phi
          (C.gamma (D.gammaIndex d)) d.1).connectedComponentMk
          (Sum.inl (D.v0 d))
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj₂).symm.trans hf2c
    have hv2tree : R.v2 ∈ TreeSequenceVertexSet T := by
      have hrem : R.v2 ∈ TreeSequenceVertexSet T ∧
          R.v2 ≠ C.blockVertex (D.gammaIndex d) 0 ∧
          R.v2 ≠ C.blockVertex (D.gammaIndex d) 1 := by
        simpa using R.v2_in_remainder
      exact hrem.1
    have hv2 : R.v2 = D.v0 d :=
      ScheideDefectiveTailExternal G k e0 phi T C D d R.v2 hv2tree hv2c
    have hf0v : Incident G (D.v0 d) (D.f0 d) := by
      change D.v0 d ∈ G.ends (D.f0 d)
      rw [D.f0_ends]
      simp []
    have hadj : AdjacentEdges G (D.f0 d) R.f2 :=
      ⟨D.v0 d, hf0v, hv2 ▸ hf2v⟩
    have hbad := hproper R.f0_ne_f2 hadj (D.f0_color d)
    exact hbad R.f2_color
  have edge_not :
    ∀ (u : V) (e : E), Incident G u e → Sum.inl u ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex
        d)) d.1 (Sum.inl (D.v0 d)) → Sum.inr e ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex
        d)) d.1 (Sum.inl (D.v0 d)) := by
    intro u e hue huc hec
    let H := TwoColorIncidenceGraph G phi (C.gamma (D.gammaIndex d)) d.1
    have hr : H.Reachable (Sum.inl (D.v0 d)) (Sum.inr e) := by
      apply SimpleGraph.ConnectedComponent.eq.mp
      change H.connectedComponentMk (Sum.inr e) =
        H.connectedComponentMk (Sum.inl (D.v0 d)) at hec
      exact hec.symm
    have hne : Sum.inl (D.v0 d) ≠ Sum.inr e := by
      intro h
      cases h
    have hs : Sum.inr e ∈ H.support :=
      SimpleGraph.mem_support_of_reachable hne.symm hr.symm
    obtain ⟨w, hw⟩ := H.mem_support.mp hs
    have hcol : phi e = some (C.gamma (D.gammaIndex d)) ∨
        phi e = some d.1 := by
      cases w with
      | inl w =>
          exact hw.2
      | inr w =>
          simp [H, TwoColorIncidenceGraph] at hw
    have ha : H.Adj (Sum.inl u) (Sum.inr e) := by
      simp [H, TwoColorIncidenceGraph, hue, hcol]
    apply huc
    change H.connectedComponentMk (Sum.inl u) =
      H.connectedComponentMk (Sum.inl (D.v0 d))
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).trans hec
  unfold TwoColorComponentSwap
  rcases hf with hf | hf
  · simp [edge_not R.u1 f hf no_u1]
  · simp [edge_not R.u2 f hf no_u2]

end GoldbergSeymour

end
