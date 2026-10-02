/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.Cancellation
public import LeanPool.DrossFractionalTriangleDecomposition.Internal.TransferBound
import Mathlib.Tactic.Ring

/-!
# Edge coverage by reconstructed triangle weights

The doubled on-edge transfer and off-edge cancellation reduce coverage to
flow conservation at the edge node.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The total K₄ transfer through a fixed graph edge is twice its flow excess. -/
public theorem triWeight_transfer_eq (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ))
    (hF : F.value = demand G wΔ) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
      (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
        (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
          F.f (Ghat.edge e'') (Ghat.edge e') else 0)) else 0) =
      2 * ((triThrough G e : ℝ) * wΔ - 1) := by
  have hkey :
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
        (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
          (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
            F.f (Ghat.edge e'') (Ghat.edge e') else 0)) else 0) =
      2 * ∑ e' : Sym2 V, F.f (Ghat.edge e) (Ghat.edge e') := by
    have hsplit :
        (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
          (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
            (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
              F.f (Ghat.edge e'') (Ghat.edge e') else 0)) else 0) =
        (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
          (∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
            F.f (Ghat.edge e) (Ghat.edge e') else 0) else 0) +
        (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
          (∑ e'' ∈ (triEdges t).erase e, ∑ e' : Sym2 V,
            if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
              F.f (Ghat.edge e'') (Ghat.edge e') else 0) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      by_cases het : e ∈ triEdges t
      · rw [ite_eq_left het, ite_eq_left het, ite_eq_left het,
          ← Finset.add_sum_erase (triEdges t) _ het]
      · rw [ite_eq_right het, ite_eq_right het, ite_eq_right het, add_zero]
    rw [hsplit, hkey_double G wΔ F e, hkey_cancel G wΔ F e, add_zero]
  rw [hkey, edgeNode_flow_sum G wΔ hbal F hF he]

/-- The reconstructed triangle weights sum to one on each graph edge. -/
public theorem triWeight_coverage (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ))
    (hF : F.value = demand G wΔ) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then triWeight G wΔ F t else 0) = 1 := by
  have hrw :
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then triWeight G wΔ F t else 0) =
      ∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
        (wΔ - (1 / 2) * (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
          (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
            F.f (Ghat.edge e'') (Ghat.edge e') else 0))) else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [triWeight, ite_eq_left ht]
  rw [hrw]
  have hsplit : ∀ t : Finset V,
      (if e ∈ triEdges t then
        (wΔ - (1 / 2) * (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
          (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
            F.f (Ghat.edge e'') (Ghat.edge e') else 0))) else 0) =
      (if e ∈ triEdges t then wΔ else 0) -
        (1 / 2) * (if e ∈ triEdges t then
          (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
            (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
              F.f (Ghat.edge e'') (Ghat.edge e') else 0)) else 0) := by
    intro t
    by_cases hc : e ∈ triEdges t <;> simp [hc]
  rw [Finset.sum_congr rfl (fun t _ => hsplit t), Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [triWeight_transfer_eq G wΔ hbal F hF e he]
  have hA : (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then wΔ else 0) =
      (triThrough G e : ℝ) * wΔ := by
    rw [← Finset.sum_filter, Finset.sum_const, triThrough, nsmul_eq_mul]
  rw [hA]
  ring

/-- A demand-saturating flow yields a fractional triangle decomposition. -/
public theorem decomp_of_maxflowM (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) (hwΔ : 0 < wΔ) (hmd2 : 2 ≤ G.minDegree)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    FractionalTriangleDecomp G :=
  ⟨triWeight G wΔ F, triWeight_nonneg G wΔ hwΔ hmd2 F hNoHDT,
    fun e he => triWeight_coverage G wΔ hbal F hF e he⟩

end LeanPool.DrossFractionalTriangleDecomposition
