/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM15.Section3Handle

/-!
# Graph Minors XV, (3.5), in the form cited in Graph Minors XVI

Graph Minors XVI cites (3.5) of Graph Minors XV in a form with no hypothesis `φ ≤ θ` and with no
hypothesis that the boundaries of the two regions are `O`-arcs. Both follow from what that form
assumes. The sets `{a_i}` are free, so `φ ≤ θ`
(`IsFreeSet`). And `H ∩ bd(Λ)` is a circuit whose point set is all of `bd(Λ)`, because each point of
`bd(Λ)` is a vertex or lies on an edge in `bd(Λ)` (`interSet_subBd_U`).
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe u v w

variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- For a region `Λ`, the boundary `bd(Λ)` is the point set of `H ∩ bd(Λ)`. -/
theorem interSet_subBd_U (hS : IsClosedSurface S) {H : Drawing S} {Λ : Set S}
  (hΛ : Λ ∈ H.R) : (H.interSet (subBd Λ)).U = subBd Λ := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcl : IsClosed (subBd Λ) := by
    rw [subBd_eq_frontier]
    exact isClosed_frontier
  refine Subset.antisymm (interSet_U_subset hcl) fun x hx => ?_
  have hxU : x ∈ H.U := by
    by_contra hz
    obtain ⟨r, hr, hzr⟩ := GM11.exists_region_of_notMem hz
    obtain ⟨y, hyr, hyΛ⟩ := mem_closure_iff.mp hx.1 r (GM11.region_isOpen hr) hzr
    have hrΛ : r = Λ := GM11.region_eq_of_mem hr hΛ hyr hyΛ
    have hzΛ : x ∈ Λ := hrΛ ▸ hzr
    have hzf : x ∈ frontier Λ := subBd_eq_frontier Λ ▸ hx
    exact ((GM11.region_isOpen hΛ).interior_eq ▸ hzf.2) hzΛ
  by_cases hxV : x ∈ H.V
  · exact (H.interSet (subBd Λ)).V_subset_U (mem_interSet_V hxV hx)
  obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxU hxV
  have heU : e ⊆ H.U := subset_closure.trans (H.closure_subset_U he)
  have hcle : e ⊆ closure Λ := edge_subset_closure_of_incident hS he hΛ ⟨x, hxe, hx.1⟩
  have hsub : e ⊆ subBd Λ := fun y hy => ⟨hcle hy, subset_closure ⟨mem_univ y, fun hyΛ
    => region_subset hΛ hyΛ (heU hy)⟩⟩
  have hE : e ∈ (H.interSet (subBd Λ)).E := mem_interSet_E_iff.2 ⟨he, hsub⟩
  exact (H.interSet (subBd Λ)).closure_subset_U hE (subset_closure hxe)

/-- **Graph Minors XV, (3.5)**, in the form of `GM16.GM15Theorem35Statement`. -/
theorem gm15Theorem35 : GM16.GM15Theorem35Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ φ T_star T d Λ₁ Λ₂ P a b hSpan hMet hΛ₁ hΛ₂ hne hC₁ hC₂ hNo hLine
    hφ hia hib hOa hOb hmem hP hdis hFa hFb
  have hS : IsClosedSurface S :=
    ⟨hSpan.isSurface.1, hSpan.isSurface.2.1, fun x => by_contra fun hx
      => Set.eq_empty_iff_forall_notMem.mp hSpan.bd_empty x hx⟩
  have := hSpan.isConnected
  have hcl : ∀ Λ : Set S, IsClosed (subBd Λ) := fun Λ => by
    rw [subBd_eq_frontier]
    exact isClosed_frontier
  have hO₁ : IsOArc (subBd Λ₁) := interSet_subBd_U hS hΛ₁ ▸ IsCircuit.isOArc_U hC₁
  have hO₂ : IsOArc (subBd Λ₂) := interSet_subBd_U hS hΛ₂ ▸ IsCircuit.isOArc_U hC₂
  have hle : φ ≤ θ := by
    have := hFa.2.1
    rwa [ncard_range_of_injective hia, Nat.card_fin] at this
  have hV : ∀ {Λ : Set S} {x : S}, x ∈ (H.interSet (subBd Λ)).V ↔ x ∈ H.V ∩ subBd Λ := fun {Λ x}
    => mem_interSet_V_iff (hcl Λ)
  refine GraphMinor.GM15.theorem_3_5_proof.{u, v, w} G H η θ_star θ φ T_star T Λ₁ Λ₂ P a b hSpan
    hΛ₁ hΛ₂ hne hO₁ hO₂ hC₁ hC₂ ?_ hLine hφ hle (List.nodup_ofFn.2 hia)
      (List.nodup_ofFn.2 hib) hOa hOb
    (fun i => ⟨hV.1 (hmem i).1, hV.1 (hmem i).2⟩) hP hdis hFa hFb
  rintro r hr ⟨x, hxr, hx⟩
  refine Set.disjoint_left.mpr fun y hyr hy => hNo r hr ⟨⟨x, hV.2 hx, hxr⟩, y, hV.2 hy, hyr⟩

end GraphMinor.GM16
