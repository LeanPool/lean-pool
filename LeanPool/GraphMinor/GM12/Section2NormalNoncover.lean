/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section6

/-!
# Three small sides bounded by normal curves cannot cover the surface

Case 2 of XII (2.1), page 244, applies the second tangle axiom to the
three discs of a theta graph. Normality puts each graph edge wholly
inside or outside every disc. A cover of the surface would therefore
make the three small sides cover the entire graph, contradicting that
axiom.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] {Γ : PaintingOrDrawing S}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}

/-- An edge lies wholly inside or outside a closed set with normal
frontier, because it is connected and misses the frontier. -/
theorem edge_subset_or_disjoint_of_normal_frontier {Δ : Set S} (hΔ : IsClosed Δ)
    (hb : Γ.IsNormal (frontier Δ)) {e : Set S} (he : e ∈ Γ.E) :
    e ⊆ Δ ∨ Disjoint e Δ :=
  GM11.edge_subset_or_disjoint_of_normal_frontier hΔ hb he

/-- The second tangle axiom excludes three small closed sides with
normal frontiers covering the surface. This is the non-cover step in
Case 2 of XII (2.1), page 244. -/
theorem not_support_subset_of_normal_frontiers (hT : IsPretangle Γ.toHypergraph θ T)
    {Δ₁ Δ₂ Δ₃ : Set S} (c₁ : IsClosed Δ₁) (c₂ : IsClosed Δ₂) (c₃ : IsClosed Δ₃)
    (b₁ : Γ.IsNormal (frontier Δ₁)) (b₂ : Γ.IsNormal (frontier Δ₂)) (b₃ : Γ.IsNormal (frontier Δ₃))
    (m₁ : (Γ.inter Δ₁, Γ.interOutside Δ₁) ∈ T) (m₂ : (Γ.inter Δ₂, Γ.interOutside Δ₂) ∈ T)
    (m₃ : (Γ.inter Δ₃, Γ.interOutside Δ₃) ∈ T) (hcov : Γ.U ⊆ Δ₁ ∪ Δ₂ ∪ Δ₃) : False :=
  GM11.not_support_subset_of_normal_frontiers hT c₁ c₂ c₃ b₁ b₂ b₃ m₁ m₂ m₃ hcov

/-- Three small closed sides with normal frontiers cannot cover the
surface. This is the non-cover step in XII (2.1), Case 2, page 244. -/
theorem not_cover_of_normal_frontiers (hT : IsPretangle Γ.toHypergraph θ T)
    {Δ₁ Δ₂ Δ₃ : Set S} (c₁ : IsClosed Δ₁) (c₂ : IsClosed Δ₂) (c₃ : IsClosed Δ₃)
    (b₁ : Γ.IsNormal (frontier Δ₁)) (b₂ : Γ.IsNormal (frontier Δ₂)) (b₃ : Γ.IsNormal (frontier Δ₃))
    (m₁ : (Γ.inter Δ₁, Γ.interOutside Δ₁) ∈ T) (m₂ : (Γ.inter Δ₂, Γ.interOutside Δ₂) ∈ T)
    (m₃ : (Γ.inter Δ₃, Γ.interOutside Δ₃) ∈ T) (hcov : Δ₁ ∪ Δ₂ ∪ Δ₃ = univ) : False := by
  apply not_support_subset_of_normal_frontiers hT c₁ c₂ c₃ b₁ b₂ b₃ m₁ m₂ m₃
  rw [hcov]
  exact subset_univ _

/-- Two small sides bounded by normal frontiers leave a point of the
original drawing outside both. This supplies the common outside point
in the deformation comparison of XII (2.1), Case 1, page 244. -/
theorem exists_support_point_outside_two_small_sides
    (hT : IsPretangle Γ.toHypergraph θ T)
    {D E : Set S} (hD : IsClosed D) (hE : IsClosed E)
    (hnD : Γ.IsNormal (frontier D)) (hnE : Γ.IsNormal (frontier E))
    (hmD : (Γ.inter D, Γ.interOutside D) ∈ T)
    (hmE : (Γ.inter E, Γ.interOutside E) ∈ T) :
    ∃ q ∈ Γ.U, q ∉ D ∧ q ∉ E := by
  have hnot : ¬ Γ.U ⊆ D ∪ E := by
    intro hsub
    apply not_support_subset_of_normal_frontiers hT hD hE hE hnD hnE hnE hmD hmE hmE
    intro x hx
    exact Or.inl (hsub hx)
  obtain ⟨q, hq, hqnot⟩ := Set.not_subset.mp hnot
  exact ⟨q, hq, fun h => hqnot (Or.inl h), fun h => hqnot (Or.inr h)⟩

end GraphMinor.GM12
