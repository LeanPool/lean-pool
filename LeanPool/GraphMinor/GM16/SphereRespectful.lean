/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.GM11.Theorem61
import LeanPool.GraphMinor.Surface.Schoenflies

/-!
# Tangles in sphere drawings are respectful

An `O`-arc in a sphere bounds two complementary closed discs.
If it meets a drawing only at fewer than `θ` vertices, those discs
give a separation of order less than `θ`. The first tangle axiom
chooses one side. This proves the respectfulness used for the sphere
span at the end of XVI (4.2), page 54.
-/

public section
namespace GraphMinor.GM16
open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10
universe u

/-- The respectfulness step at the end of XVI (4.2), page 54:
every tangle in a drawing in a sphere is respectful. -/
theorem drawing_tangle_isRespectful_of_isSphere
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) (D : Drawing S) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle D.toHypergraph θ T) :
    (PaintingOrDrawing.drawing D).IsRespectful θ T := by
  let Γ := PaintingOrDrawing.drawing D
  refine ⟨inferInstance,fun F hF hN hk => ?_⟩
  have hSepDisc (Δ : Set S) (hΔ : IsClosedDisc Δ) (hb : discBd Δ = F) :
      Γ.toHypergraph.IsSeparation (Γ.inter Δ) (Γ.interOutside Δ) ∧
      separationOrder (Γ.inter Δ) (Γ.interOutside Δ) < θ := by
    have hFr : frontier Δ = F := by rw [IsClosedDisc.frontier_eq_discBd hS hΔ,hb]
    refine ⟨isSeparation_inter (IsClosedDisc.isCompact hΔ).isClosed (by rw [hFr]; exact hN),?_⟩
    refine (ncard_le_ncard (fun x hx => ?_) (D.finite_V.subset inter_subset_right)).trans_lt hk
    rw [← hFr]
    exact inter_outside_subset hx
  have hBd (Δ : Set S) (hΔ : IsClosedDisc Δ) : subBd Δ = discBd Δ := by
    rw [subBd_eq_frontier,IsClosedDisc.frontier_eq_discBd hS hΔ]
  obtain ⟨Δ₁,Δ₂,_,hΔ₁,hΔ₂,hb₁,hb₂,hCup,hCap,_,_⟩ := sphere_disc S hSphere F hF
  have outside {Δ Δ' : Set S} (h : IsClosedDisc Δ) (h' : IsClosedDisc Δ')
      (hb' : discBd Δ' = F) (hUnion : Δ ∪ Δ' = univ) (hInter : Δ ∩ Δ' = F) :
      closure (univ \ Δ) = Δ' := by
    apply Subset.antisymm
    · exact closure_minimal (fun x hx => (hUnion.ge (mem_univ x)).resolve_left hx.2)
        (IsClosedDisc.isCompact h').isClosed
    · refine (IsClosedDisc.subset_closure_discInt h').trans (closure_mono ?_)
      intro x hx
      refine ⟨mem_univ x,fun hxΔ => hx.2 ?_⟩
      rw [hb',← hInter]
      exact ⟨hxΔ,hx.1⟩
  have h₁₂ := outside hΔ₁ hΔ₂ hb₂ hCup hCap
  have h₂₁ := outside hΔ₂ hΔ₁ hb₁ (by rw [Set.union_comm,hCup]) (by rw [Set.inter_comm,hCap])
  obtain ⟨hSep,hOrd⟩ := hSepDisc Δ₁ hΔ₁ hb₁
  rcases hT.axiom1 hSep hOrd with hm | hm
  · exact ⟨Δ₁,hΔ₁,(hBd _ hΔ₁).trans hb₁,hm⟩
  · refine ⟨Δ₂,hΔ₂,(hBd _ hΔ₂).trans hb₂,?_⟩
    have hOut₁ : Γ.interOutside Δ₁ = Γ.inter Δ₂ := by rw [PaintingOrDrawing.interOutside,h₁₂]
    have hOut₂ : Γ.interOutside Δ₂ = Γ.inter Δ₁ := by rw [PaintingOrDrawing.interOutside,h₂₁]
    rw [hOut₂]
    rwa [hOut₁] at hm

end GraphMinor.GM16
