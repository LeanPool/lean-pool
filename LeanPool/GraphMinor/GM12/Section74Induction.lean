/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section74Base
import LeanPool.GraphMinor.GM12.Section74Components
import LeanPool.GraphMinor.GM12.Section74DiscRegion
import LeanPool.GraphMinor.GM12.Section73VertexReduction
import LeanPool.GraphMinor.GM12.Section73DiscPreprocess
import LeanPool.GraphMinor.GM11.Section810

/-!
# The disc-removal induction step of XII (7.4)

On page 263, remove a selected normal disc through the vertex
that contains an old edge. Its outside restriction has fewer
edges. Apply (7.2), then the induction hypothesis to this smaller
drawing. Components are preserved across the normal boundary.
The final region absorbs the removed disc. The shared-atom
lower bounds compose, and the lost-atom bound from (7.2) proves
the remaining upper bound for old atoms in the final region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14

/-- The disc-removal case of the edge induction proving XII
(7.4), page 263. The induction hypothesis is quantified over
all drawings with strictly fewer edges and the same order. -/
theorem theorem_7_4_disc_induction
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V)
    (hInd : ∀ (Λ : Drawing S)
      (U : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (δ : Set S → Set S → ℕ),
      Λ.E.ncard < Γ.E.ncard → HasTangleMetric Λ θ U δ → v ∈ Λ.V →
      ∃ (H : Drawing S) (U' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (δ' : Set S → Set S → ℕ) (s : Set S),
        H.IsSubdrawing (deleteVertices Λ {v}) ∧ H.U ∈ componentsIn (deleteVertices Λ {v}).U ∧
        HasTangleMetric H (θ - 1) U' δ' ∧ s ∈ H.R ∧ v ∈ s ∧ Λ.U ⊆ H.U ∪ s ∧
        (∀ a ∈ Λ.A ∩ H.A, ∀ b ∈ Λ.A ∩ H.A, δ a b - 2 ≤ δ' a b) ∧
        (∀ a ∈ Λ.A ∩ H.A, δ a {v} - 1 ≤ δ' a s) ∧
        (∀ a ∈ Λ.A, a ⊆ s → δ a {v} ≤ 2))
    {D F : Set S} (hD : IsClosedDisc D) (hF : IsOArc F) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    {e : Set S} (he : e ∈ Γ.E) (heD : e ⊆ D) :
    ∃ (Γ' : Drawing S) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧ Γ'.U ∈ componentsIn (deleteVertices Γ {v}).U ∧
      HasTangleMetric Γ' (θ - 1) T' d' ∧ r ∈ Γ'.R ∧ v ∈ r ∧ Γ.U ⊆ Γ'.U ∪ r ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r) ∧
      (∀ a ∈ Γ.A, a ⊆ r → d a {v} ≤ 2) := by
  obtain ⟨r₀, hr₀, hFr⟩ := exists_region_of_normal_circle_single_vertex hF hn hFV
  obtain ⟨_, hlost, d₀, _, hd₀, _, _, hcomp, _⟩ :=
    theorem_7_2_proof hS hθ hd hD hbd hn hFV hr₀ hFr hm
  let Λ := Γ.interSet (closure (univ \ D))
  have hΛΓ : Λ.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hvΛ : v ∈ Λ.V := by
    apply (mem_interSet_V_iff isClosed_closure).mpr
    have hvF : v ∈ F := (hFV.symm ▸ mem_singleton v).1
    have hvfr : v ∈ frontier D := ((subBd_eq_frontier D).symm.trans hbd).symm ▸ hvF
    rw [frontier_eq_closure_inter_closure] at hvfr
    exact ⟨hv, by simpa only [compl_eq_univ_sdiff] using hvfr.2⟩
  have hsmall : Λ.E.ncard < Γ.E.ncard := ncard_edges_outside_lt_of_edge_inside
    (fun x hx => hn ⟨((subBd_eq_frontier D).symm.trans hbd) ▸ hx.1, hx.2⟩) he heD
  obtain ⟨Γ', T', d', r, hΓ'Λ, hcomponent, hd', hr, hvr, hcover, hi, hii, hiii⟩ :=
    hInd Λ _ d₀ hsmall hd₀ hvΛ
  have hΓ' : Γ'.IsSubdrawing Λ := hΓ'Λ.trans (deleteVertices_isSubdrawing Λ {v})
  have hΓ'Γ : Γ'.IsSubdrawing Γ := hΓ'.trans hΛΓ
  have hdelete : Γ'.IsSubdrawing (deleteVertices Γ {v}) := by
    apply isSubdrawing_deleteVertices_iff.mpr
    exact ⟨hΓ'Γ, (isSubdrawing_deleteVertices_iff.mp hΓ'Λ).2⟩
  have hshared : ∀ a ∈ Γ.A ∩ Γ'.A, a ∈ Λ.A ∩ Γ'.A := by
    intro a ha
    exact ⟨shared_atom_mem_intermediate hΛΓ hΓ' ha.1 ha.2, ha.2⟩
  have hDr := normal_disc_subset_final_vertex_region hS hD hbd hn hFV hr₀ hFr hΓ' hr hvr
  have hcoverΓ : Γ.U ⊆ Γ'.U ∪ r := by
    intro x hx
    rcases drawing_subset_outside_disc_union_disc hbd hn hx with hxΛ | hxD
    · exact hcover hxΛ
    · exact Or.inr (hDr (Or.inr hxD))
  have hvA : ({v} : Set S) ∈ Γ.A ∩ Λ.A :=
    ⟨Or.inl (Or.inl ⟨v, hv, rfl⟩), Or.inl (Or.inl ⟨v, hvΛ, rfl⟩)⟩
  refine ⟨Γ', T', d', r, hdelete,
    component_after_normal_disc_reduction hbd hn hFV hcomponent,
    hd', hr, hvr, hcoverΓ, ?_, ?_, ?_⟩
  · intro a ha b hb
    have haΛ := hshared a ha
    have hbΛ := hshared b hb
    have hle := hcomp a ⟨ha.1, haΛ.1⟩ b ⟨hb.1, hbΛ.1⟩
    have hbound := hi a haΛ b hbΛ
    omega
  · intro a ha
    have haΛ := hshared a ha
    have hle := hcomp a ⟨ha.1, haΛ.1⟩ {v} hvA
    have hbound := hii a haΛ
    omega
  · intro a ha har
    by_cases haΛ : a ∈ Λ.A
    · have hle := hcomp a ⟨ha, haΛ⟩ {v} hvA
      have hbound := hiii a haΛ har
      omega
    · exact (hlost a ⟨ha, haΛ⟩).trans (by decide)

end GraphMinor.GM12
