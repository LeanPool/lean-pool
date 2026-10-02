/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.ExactCutBound

/-!
# A flow meeting the exact Dross demand

The source cut has capacity equal to demand. The exact lower bound for all cuts
and max-flow/min-cut therefore produce a flow of that value.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The source cut has capacity exactly the network demand. -/
public theorem srcCut_capacity (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) :
    (⟨{Ghat.src}, by simp [drossNet], by simp [drossNet]⟩ :
      Contrib.MaxFlowMinCut.Cut (drossNet G wΔ)).capacity = demand G wΔ := by
  change ∑ u ∈ {Ghat.src}, ∑ v ∈ Finset.univ \ {Ghat.src}, dcap G wΔ u v = demand G wΔ
  rw [Finset.sum_singleton, Finset.sum_sdiff_eq_sub (by simp), Finset.sum_singleton]
  have hss : dcap G wΔ Ghat.src Ghat.src = 0 := rfl
  rw [hss, sub_zero, sum_Ghat (fun v => dcap G wΔ Ghat.src v)]
  simp only [hss, show dcap G wΔ Ghat.src Ghat.snk = 0 from rfl, zero_add,
    show ∀ e, dcap G wΔ Ghat.src (Ghat.edge e) =
      max ((triThrough G e : ℝ) * wΔ - 1) 0 from fun _ => rfl]
  rw [demand]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  rw [triThrough_eq_zero_of_notMem G he]
  simp

/-- The auxiliary network has a flow whose value is exactly its demand. -/
public theorem exists_flow_M_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10)
    (hn20 : 20 ≤ Fintype.card V) (hmd2 : 2 ≤ G.minDegree)
    (hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hmbound : 2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ ^ 2) * (Fintype.card V : ℝ) ^ 2 + 4 + (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ)) :
    ∃ F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ), F.value = demand G wΔ := by
  obtain ⟨F, C, hFC⟩ := Contrib.MaxFlowMinCut.maxflow_eq_mincut (drossNet G wΔ)
  refine ⟨F, le_antisymm ?_ ?_⟩
  · have hsrc := Contrib.MaxFlowMinCut.value_le_capacity F
      (⟨{Ghat.src}, by simp [drossNet], by simp [drossNet]⟩ :
        Contrib.MaxFlowMinCut.Cut (drossNet G wΔ))
    rwa [srcCut_capacity] at hsrc
  · rw [hFC]
    exact cut_ge_M_exact G h wΔ hwΔ hbal δ hδ0 hδ1 hn20 hmd2 hδ_eq hmbound C

end LeanPool.DrossFractionalTriangleDecomposition
