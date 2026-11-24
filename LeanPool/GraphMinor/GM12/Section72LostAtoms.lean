/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72TwoCell
public import LeanPool.GraphMinor.GM12.Section76
import LeanPool.GraphMinor.GM12.Section79

/-!
# Lost atoms are at distance at most one in XII (7.2)

Every old atom lost by the outside restriction lies in the merged
region. It meets the selected inside disc: either it is the old region,
or it lies in the punctured disc. The trace of the boundary circle
therefore bounds its distance from the one boundary vertex by one.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The lost-atom bound in XII (7.2), pages 259–260. The selected disc and
its boundary vertex meet every lost atom, so the normal-circle bound
from (2.1) gives distance at most one. -/
theorem theorem_7_2_lost_atoms (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {Δ F r : Set S} {v : S} (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hFV : F ∩ Γ.V = {v}) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T)
    {a : Set S} (ha : a ∈ Γ.A)
    (han : a ∉ (Γ.interSet (closure (univ \ Δ))).A) : d a {v} ≤ 1 := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let Γ' := Γ.interSet (closure (univ \ Δ))
  let Y := r ∪ (Δ \ {v})
  have hsub : Γ'.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hY : Y ∈ Γ'.R := theorem_7_2_region hS hΔ hbd hn hFV hr hFr
  have hfr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hdb : discBd Δ = F := (IsClosedDisc.frontier_eq_discBd hS hΔ).symm.trans hfr
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hvD : v ∈ Δ := Surface.discBd_subset Δ (hdb.symm ▸ hvFV.1)
  have hnorm : frontier (closure (univ \ Δ)) ∩ Γ.U ⊆ Γ.V := by
    rw [← compl_eq_univ_sdiff, closure_compl, frontier_compl]
    exact fun x hx => hn ⟨hfr ▸ frontier_interior_subset hx.1, hx.2⟩
  have hUeq := interSet_U_eq_of_normal_frontier isClosed_closure hnorm
  have hcover : Γ.U ⊆ Γ'.U ∪ Y := by
    intro x hx
    by_cases hxout : x ∈ closure (univ \ Δ)
    · exact Or.inl (hUeq.symm ▸ ⟨hx, hxout⟩)
    · have hxi : x ∈ interior Δ := by
        by_contra h
        exact hxout (by rw [← compl_eq_univ_sdiff, closure_compl]; exact h)
      exact Or.inr (Or.inr ⟨interior_subset hxi, fun hxv =>
        (hfr.symm ▸ hvFV.1).2 (mem_singleton_iff.mp hxv ▸ hxi)⟩)
  obtain ⟨a', ha', haa'⟩ := exists_atom_superset_of_isSubdrawing hsub ha
  have haY : a ⊆ Y := by
    rcases atom_eq_or_eq_region_of_U_subset hsub hY hcover ha ha' haa' with
      ⟨_, hmem⟩ | ⟨_, haY⟩
    · exact (han hmem.2).elim
    · exact haY
  have haD : (a ∩ Δ).Nonempty := by
    obtain ⟨x, hxa⟩ := atom_nonempty' ha
    rcases haY hxa with hxr | hxD
    · have heq : a = r := atom_eq_of_inter_nonempty ha (Or.inr hr) ⟨x, hxa, hxr⟩
      obtain ⟨w, hw, hwv⟩ := (infinite_of_isOArc hΔ.isOArc_discBd).exists_notMem_finite
        (finite_singleton v)
      exact ⟨w, heq.symm ▸ hFr ⟨hdb ▸ hw, hwv⟩, Surface.discBd_subset Δ hw⟩
    · exact ⟨x, hxa, hxD.1⟩
  have hcard : (F ∩ Γ.V).ncard < θ := by rw [hFV, ncard_singleton]; omega
  have hbound := dist_le_of_oarc_disc hS hd (hdb ▸ hΔ.isOArc_discBd) hn hcard hΔ hbd hm ha
    (Or.inl (Or.inl ⟨v, hvFV.2, rfl⟩)) haD ⟨v, rfl, hvD⟩
  simpa only [hFV, ncard_singleton] using hbound

end GraphMinor.GM12
