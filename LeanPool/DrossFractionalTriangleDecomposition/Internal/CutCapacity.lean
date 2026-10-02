/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.CutBridges

/-!
# The three families of arcs crossing a Dross cut

Every cut has at least the capacity contributed by source-to-B, A-to-sink,
and rooted-K₄ arcs from A to B.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Real graph edges whose network nodes lie on the source side. -/
@[expose] public def cutA (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) (C : Contrib.MaxFlowMinCut.Cut (drossNet G wΔ)) :
    Finset (Sym2 V) := G.edgeFinset.filter (fun e => Ghat.edge e ∈ C.S)

/-- Edges of `G` whose node lies on the sink side `B` of the cut. -/
@[expose] public def cutB (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) (C : Contrib.MaxFlowMinCut.Cut (drossNet G wΔ)) :
    Finset (Sym2 V) := G.edgeFinset.filter (fun e => Ghat.edge e ∉ C.S)

/-- **Capacity decomposition (lower bound).** The capacity of any s–t cut is at least the sum of
its three arc families: source→B, A→sink, and the K₄ arcs from A to B. (Non-edge nodes and the
`src→snk` arc only add nonnegative slack, hence a lower bound.) -/
public theorem capacity_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (C : Contrib.MaxFlowMinCut.Cut (drossNet G wΔ)) :
    (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
      + (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
      + (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C,
          if K4pair G e e' then max (cc G wΔ) 0 else 0)
      ≤ C.capacity := by
  have hnn : ∀ u v, 0 ≤ dcap G wΔ u v := (drossNet G wΔ).capNonneg
  have hinj : ∀ a ∈ cutA G wΔ C, ∀ b ∈ cutA G wΔ C, Ghat.edge a = Ghat.edge b → a = b :=
    fun a _ b _ hab => by injection hab
  have hinjB : ∀ a ∈ cutB G wΔ C, ∀ b ∈ cutB G wΔ C, Ghat.edge a = Ghat.edge b → a = b :=
    fun a _ b _ hab => by injection hab
  -- S0 ⊆ C.S : source node plus the A-side edge nodes
  have hsrc_notin : Ghat.src ∉ (cutA G wΔ C).image Ghat.edge := by simp
  have hsub : insert Ghat.src ((cutA G wΔ C).image Ghat.edge) ⊆ C.S := by
    rw [Finset.insert_subset_iff]
    refine ⟨C.hs, fun x hx => ?_⟩
    rw [Finset.mem_image] at hx; obtain ⟨e, he, rfl⟩ := hx
    exact (Finset.mem_filter.mp he).2
  -- capacity ≥ sum over S0
  have step1 : ∑ u ∈ insert Ghat.src ((cutA G wΔ C).image Ghat.edge),
      ∑ v ∈ Finset.univ \ C.S, dcap G wΔ u v ≤ C.capacity :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun u _ _ => Finset.sum_nonneg (fun v _ => hnn u v))
  -- split the S0-sum into the source row and the A-edge rows
  have hS0 : ∑ u ∈ insert Ghat.src ((cutA G wΔ C).image Ghat.edge),
        ∑ v ∈ Finset.univ \ C.S, dcap G wΔ u v
      = (∑ v ∈ Finset.univ \ C.S, dcap G wΔ Ghat.src v)
        + ∑ e ∈ cutA G wΔ C, ∑ v ∈ Finset.univ \ C.S, dcap G wΔ (Ghat.edge e) v := by
    rw [Finset.sum_insert hsrc_notin, Finset.sum_image hinj]
  -- source row ≥ source→B sum
  have hsubB : (cutB G wΔ C).image Ghat.edge ⊆ Finset.univ \ C.S := by
    intro x hx
    rw [Finset.mem_image] at hx; obtain ⟨e, he, rfl⟩ := hx
    rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩
  have hsrcrow : ∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0
      ≤ ∑ v ∈ Finset.univ \ C.S, dcap G wΔ Ghat.src v := by
    calc ∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0
        = ∑ e ∈ cutB G wΔ C, dcap G wΔ Ghat.src (Ghat.edge e) := rfl
      _ = ∑ v ∈ (cutB G wΔ C).image Ghat.edge, dcap G wΔ Ghat.src v :=
          (Finset.sum_image hinjB).symm
      _ ≤ ∑ v ∈ Finset.univ \ C.S, dcap G wΔ Ghat.src v :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubB (fun v _ _ => hnn _ _)
  -- each A-edge row ≥ (sink term) + (K₄ arcs to B)
  have hedgerow : ∀ e ∈ cutA G wΔ C,
      max (1 - (triThrough G e : ℝ) * wΔ) 0
        + (∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
      ≤ ∑ v ∈ Finset.univ \ C.S, dcap G wΔ (Ghat.edge e) v := by
    intro e _
    have hsnk_notin : Ghat.snk ∉ (cutB G wΔ C).image Ghat.edge := by simp
    have hunion_sub : insert Ghat.snk ((cutB G wΔ C).image Ghat.edge) ⊆ Finset.univ \ C.S := by
      rw [Finset.insert_subset_iff]
      refine ⟨by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, C.ht⟩, ?_⟩
      intro x hx
      rw [Finset.mem_image] at hx; obtain ⟨e', he', rfl⟩ := hx
      rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp he').2⟩
    calc max (1 - (triThrough G e : ℝ) * wΔ) 0
            + (∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
        = dcap G wΔ (Ghat.edge e) Ghat.snk
            + ∑ e' ∈ cutB G wΔ C, dcap G wΔ (Ghat.edge e) (Ghat.edge e') := rfl
      _ = dcap G wΔ (Ghat.edge e) Ghat.snk
            + ∑ v ∈ (cutB G wΔ C).image Ghat.edge, dcap G wΔ (Ghat.edge e) v := by
          rw [Finset.sum_image hinjB]
      _ = ∑ v ∈ insert Ghat.snk ((cutB G wΔ C).image Ghat.edge), dcap G wΔ (Ghat.edge e) v := by
          rw [Finset.sum_insert hsnk_notin]
      _ ≤ ∑ v ∈ Finset.univ \ C.S, dcap G wΔ (Ghat.edge e) v :=
          Finset.sum_le_sum_of_subset_of_nonneg hunion_sub (fun v _ _ => hnn _ _)
  calc (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        + (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        + (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C,
            if K4pair G e e' then max (cc G wΔ) 0 else 0)
      = (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        + ∑ e ∈ cutA G wΔ C, (max (1 - (triThrough G e : ℝ) * wΔ) 0
            + ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0) := by
        rw [Finset.sum_add_distrib]; ring
    _ ≤ (∑ v ∈ Finset.univ \ C.S, dcap G wΔ Ghat.src v)
        + ∑ e ∈ cutA G wΔ C, ∑ v ∈ Finset.univ \ C.S, dcap G wΔ (Ghat.edge e) v :=
        add_le_add hsrcrow (Finset.sum_le_sum hedgerow)
    _ = ∑ u ∈ insert Ghat.src ((cutA G wΔ C).image Ghat.edge),
          ∑ v ∈ Finset.univ \ C.S, dcap G wΔ u v := hS0.symm
    _ ≤ C.capacity := step1

end LeanPool.DrossFractionalTriangleDecomposition
