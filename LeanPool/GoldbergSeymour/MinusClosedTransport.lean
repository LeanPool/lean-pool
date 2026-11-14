/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# P2813_T1_Minus Closed Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem P2813_T1_MinusClosedTransport {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (U : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta) (z : Sum V E)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (reserved : Finset (Fin k))
    (hclosed : TreeColorSetMinusClosed G phi U reserved)
    (hmissing : ∀ v ∈ TreeSequenceVertexSet U,
      MissingColors G sigma v = MissingColors G phi v)
    (houtside : ∀ c : Fin k, (c = alpha ∨ c = beta) →
      c ∈ TreeMissingColors phi U → TreeColorSetClosed G phi U {c} →
      OutsideKempeRecoloring U phi sigma alpha beta) :
    TreeColorSetMinusClosed G sigma U reserved := by
  classical
  have hm : TreeMissingColors sigma U = TreeMissingColors phi U := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl hmissing
  have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      sigma f = some c ↔ phi f = some c := by
    clear * - G phi sigma alpha beta hne z hsigma f c hca hcb
    rw [hsigma]
    by_cases hf : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
    · by_cases ha : phi f = some alpha
      · simp [TwoColorComponentSwap, hf, ha, hca.symm, hcb.symm]
      · by_cases hb : phi f = some beta
        · simp [TwoColorComponentSwap, hf, hb, hne.symm, hca.symm, hcb.symm]
        · simp [TwoColorComponentSwap, hf, ha, hb]
    · simp [TwoColorComponentSwap, hf]
  intro c hc
  rw [hm] at hc
  have hcm := (Finset.mem_sdiff.mp hc).1
  have hcClosed : TreeColorSetClosed G phi U {c} := by
    intro d hd
    have hdEq : d = c := Finset.mem_singleton.mp hd
    subst d
    exact hclosed c hc
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  have hboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet U) ∧
      sigma f = some c := by simpa only [BoundaryColorEdges, Finset.mem_filter,
        Finset.mem_univ, true_and] using hf
  have hi : TreeIncidentEdge U f := by
    have hends : ∃ u ∈ TreeSequenceVertexSet U,
        ∃ v ∉ TreeSequenceVertexSet U, G.ends f = s(u, v) := by
      simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        using hboundary.1
    obtain ⟨u, hu, v, hv, he⟩ := hends
    refine ⟨u, hu, ?_⟩
    rw [Incident, he]
    exact Sym2.mem_mk_left _ _
  have hold : phi f = some c := by
    by_cases hca : c = alpha
    · have hout := houtside c (Or.inl hca) hcm hcClosed
      have hh := OutsideKempeRecoloringStable G e0 U ∅ phi sigma alpha beta hproper hone hout
      exact (hh.2.2.2.2 f hi).symm.trans hboundary.2
    · by_cases hcb : c = beta
      · have hout := houtside c (Or.inr hcb) hcm hcClosed
        have hh := OutsideKempeRecoloringStable G e0 U ∅ phi sigma alpha beta hproper hone hout
        exact (hh.2.2.2.2 f hi).symm.trans hboundary.2
      · exact (unaffected f c hca hcb).mp hboundary.2
  have hfOld : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet U) c := by
    exact Finset.mem_filter.mpr ⟨hboundary.1, hold⟩
  rw [hclosed c hc] at hfOld
  exact Finset.notMem_empty f hfOld

end GoldbergSeymour

end
