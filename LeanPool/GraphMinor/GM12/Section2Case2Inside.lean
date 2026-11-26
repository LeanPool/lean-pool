/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ThetaConstruction
public import LeanPool.GraphMinor.GM12.Section2ThetaDiscs
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The smaller selected inside in Case 2 of XII (2.1)

When a simple normal circle visits a region in more than one component,
the minimal chord produces two smaller normal circles. Respectfulness
selects discs for them. The second tangle axiom and the theta-disc union
relation show that an atom meeting the original selected disc meets
one of these smaller selected discs. This is the geometric reduction
before applying induction to their traces.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The geometric induction reduction in Case 2 of Graph Minors XII,
(2.1), page 244. A repeated region gives a strictly smaller normal circle
whose tangle-selected disc still meets the specified atom. -/
theorem theorem_2_1_case2_smaller_inside {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {F Δ C r : Set S} (hF : IsOArc F) (hFn : Γ.IsNormal F)
    (hcount : (F ∩ Γ.V).ncard < θ) (hr : r ∈ Γ.R)
    (hdisconn : ¬ IsPreconnected (F ∩ r))
    (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T)
    (hC : (C ∩ Δ).Nonempty) :
    ∃ F' Δ' : Set S, IsOArc F' ∧ Γ.IsNormal F' ∧
      (F' ∩ Γ.V).ncard < (F ∩ Γ.V).ncard ∧ IsClosedDisc Δ' ∧ subBd Δ' = F' ∧
      ((PaintingOrDrawing.drawing Γ).inter Δ',
        (PaintingOrDrawing.drawing Γ).interOutside Δ') ∈ T ∧ (C ∩ Δ').Nonempty ∧
          (F' ∩ Γ.V).Nonempty ∧
      ∃ L : Set S, IsClosed L ∧ Disjoint L Γ.V ∧ F' ⊆ F ∪ L := by
  obtain ⟨L, A, B, a, b, hL, hA, hB, hABF, hLA, hLB, hAB, hLr,
    hLAo, hLBo, hLAn, hLBn, hAV, hBV⟩ :=
    exists_theta_of_disconnected_region_intersection hS hr hF hFn hdisconn
  have hLU : Disjoint L Γ.U := Set.disjoint_left.mpr fun z hz => region_subset hr (hLr hz)
  have hLV : Disjoint L Γ.V := hLU.mono_right Γ.V_subset_U
  have hABV : Disjoint (A ∩ B) Γ.V := by
    apply Set.disjoint_left.mpr
    intro z hz hzV
    have hend : z ∈ ({a, b} : Set S) := hAB ▸ hz
    have hzL : z ∈ L := (hLA.symm ▸ hend).1
    exact Set.disjoint_left.mp hLV hzL hzV
  have hsmall := chord_circle_vertex_counts_lt Γ.finite_V hLV hABV hAV hBV
  have hcLA : ((L ∪ A) ∩ Γ.V).ncard < (F ∩ Γ.V).ncard := by
    rw [union_comm L A, ← hABF]
    exact hsmall.1
  have hcLB : ((L ∪ B) ∩ Γ.V).ncard < (F ∩ Γ.V).ncard := by
    rw [union_comm L B, ← hABF]
    exact hsmall.2
  obtain ⟨Δ₁, hd₁, hb₁, hm₁⟩ := hrespect.2 (L ∪ B) hLBo hLBn (hcLB.trans hcount)
  obtain ⟨Δ₂, hd₂, hb₂, hm₂⟩ := hrespect.2 (L ∪ A) hLAo hLAn (hcLA.trans hcount)
  have frontier_bd : ∀ {D : Set S}, IsClosedDisc D → subBd D = discBd D := by
    intro D hd
    rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hd]
  have f₀ : discBd Δ = A ∪ B := (frontier_bd hΔ).symm.trans (hbd.trans hABF.symm)
  have f₁ : discBd Δ₁ = B ∪ L :=
    (frontier_bd hd₁).symm.trans (hb₁.trans (union_comm L B))
  have f₂ : discBd Δ₂ = L ∪ A := (frontier_bd hd₂).symm.trans hb₂
  have n₀ : (PaintingOrDrawing.drawing Γ).IsNormal (discBd Δ) := by
    rw [f₀, hABF]
    exact hFn
  have n₁ : (PaintingOrDrawing.drawing Γ).IsNormal (discBd Δ₁) := by
    rw [← frontier_bd hd₁, hb₁]
    exact hLBn
  have n₂ : (PaintingOrDrawing.drawing Γ).IsNormal (discBd Δ₂) := by
    rw [f₂]
    exact hLAn
  have hiBL : B ∩ L = {a, b} := (inter_comm B L).trans hLB
  have hmeet := theorem_2_1_case2_disc_step (Γ := PaintingOrDrawing.drawing Γ) hS hT hL hA hB hLA
    hAB hiBL
    hΔ hd₁ hd₂ f₀ f₁ f₂ n₀ n₁ n₂ hm hm₁ hm₂ hC
  rcases hmeet with hmeet | hmeet
  · refine ⟨L ∪ B, Δ₁, hLBo, hLBn, hcLB, hd₁, hb₁, hm₁, hmeet,
      hBV.mono (inter_subset_inter_left Γ.V subset_union_right),
      L, hL.isCompact.isClosed, hLV, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl (hABF ▸ Or.inr hx)
  · refine ⟨L ∪ A, Δ₂, hLAo, hLAn, hcLA, hd₂, hb₂, hm₂, hmeet,
      hAV.mono (inter_subset_inter_left Γ.V subset_union_right),
      L, hL.isCompact.isClosed, hLV, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl (hABF ▸ Or.inl hx)

end GraphMinor.GM12
