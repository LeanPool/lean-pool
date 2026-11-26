/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM11.DrawingTopology
public import LeanPool.GraphMinor.GM11.Section6Pretangle

/-! Closed sides with normal frontiers give the non-cover criterion for a pretangle. -/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology Surface

variable {S : Type*} [TopologicalSpace S] {Γ : PaintingOrDrawing S} {Γ' : Drawing S}
  {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}

theorem PaintingOrDrawing.toHypergraph_inc {Γ : PaintingOrDrawing S} {e : Set S} {v : S} :
    Γ.toHypergraph.Inc e v ↔ e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e := by
  cases Γ <;> rfl

theorem PaintingOrDrawing.edge_props {Γ : PaintingOrDrawing S} {e : Set S} (he : e ∈ Γ.E) :
    IsPreconnected e ∧ Disjoint e Γ.V ∧ e ⊆ Γ.U ∧ e.Nonempty := by
  cases Γ with
  | painting Γ =>
    exact ⟨he.2.2.1.isConnected.isPreconnected, disjoint_left.mpr fun x hx => (he.2.1 hx).2,
      fun x hx => (he.2.1 hx).1, he.1⟩
  | drawing Γ =>
    exact ⟨he.2.2.1.isConnected.isPreconnected, disjoint_left.mpr fun x hx => (he.2.1 hx).2,
      fun x hx => (he.2.1 hx).1, he.1⟩

/-- An edge lies wholly inside or outside a closed set with normal
frontier, because it is connected and misses the frontier. -/
theorem edge_subset_or_disjoint_of_normal_frontier {Δ : Set S} (hΔ : IsClosed Δ)
    (hb : Γ.IsNormal (frontier Δ)) {e : Set S} (he : e ∈ Γ.E) :
    e ⊆ Δ ∨ Disjoint e Δ := by
  obtain ⟨hp, hd, hU, _⟩ := Γ.edge_props he
  apply subset_or_disjoint_of_frontier hΔ hp
  exact Set.disjoint_left.mpr fun x hx hf => Set.disjoint_left.mp hd hx (hb ⟨hf, hU hx⟩)

/-- The second tangle axiom excludes three small closed sides with
normal frontiers covering the drawing. -/
theorem not_support_subset_of_normal_frontiers (hT : IsPretangle Γ.toHypergraph θ T)
    {Δ₁ Δ₂ Δ₃ : Set S} (c₁ : IsClosed Δ₁) (c₂ : IsClosed Δ₂) (c₃ : IsClosed Δ₃)
    (b₁ : Γ.IsNormal (frontier Δ₁)) (b₂ : Γ.IsNormal (frontier Δ₂)) (b₃ : Γ.IsNormal (frontier Δ₃))
    (m₁ : (Γ.inter Δ₁, Γ.interOutside Δ₁) ∈ T) (m₂ : (Γ.inter Δ₂, Γ.interOutside Δ₂) ∈ T)
    (m₃ : (Γ.inter Δ₃, Γ.interOutside Δ₃) ∈ T) (hcov : Γ.U ⊆ Δ₁ ∪ Δ₂ ∪ Δ₃) : False := by
  have hedge : ∀ e ∈ Γ.E, e ⊆ Δ₁ ∨ e ⊆ Δ₂ ∨ e ⊆ Δ₃ := by
    intro e he
    obtain ⟨x, hx⟩ := (Γ.edge_props he).2.2.2
    have hxc : x ∈ Δ₁ ∪ Δ₂ ∪ Δ₃ := hcov ((Γ.edge_props he).2.2.1 hx)
    have side : ∀ {Δ : Set S}, IsClosed Δ → Γ.IsNormal (frontier Δ) → x ∈ Δ → e ⊆ Δ := fun c b h =>
      (edge_subset_or_disjoint_of_normal_frontier c b he).resolve_right
        fun hd => disjoint_left.mp hd hx h
    rcases hxc with (h | h) | h
    · exact Or.inl (side c₁ b₁ h)
    · exact Or.inr (Or.inl (side c₂ b₂ h))
    · exact Or.inr (Or.inr (side c₃ b₃ h))
  refine hT.axiom2 m₁ m₂ m₃ (Hypergraph.ext ?_ ?_ ?_)
  · ext v
    simp only [PaintingOrDrawing.toHypergraph_vertexSet]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hv
      have hvU : v ∈ Γ.U := by
        cases Γ with
        | painting G => exact G.V_subset_U hv
        | drawing G => exact G.V_subset_U hv
      have hvc : v ∈ Δ₁ ∪ Δ₂ ∪ Δ₃ := hcov hvU
      rcases hvc with (h | h) | h
      · exact Or.inl (Or.inl ⟨hv, h⟩)
      · exact Or.inl (Or.inr ⟨hv, h⟩)
      · exact Or.inr ⟨hv, h⟩
  · ext e
    simp only [PaintingOrDrawing.toHypergraph_edgeSet]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro he
      rcases hedge e he with h | h | h
      · exact Or.inl (Or.inl ⟨he, h⟩)
      · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr ⟨he, h⟩
  · funext e v
    apply propext
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hi
      have hcl : ∀ {Δ : Set S}, IsClosed Δ → e ⊆ Δ → v ∈ Δ := fun c h =>
        c.closure_subset_iff.mpr h (PaintingOrDrawing.toHypergraph_inc.mp hi).2.2
      rcases hedge e (PaintingOrDrawing.toHypergraph_inc.mp hi).1 with h | h | h
      · exact Or.inl (Or.inl ⟨hi, h, hcl c₁ h⟩)
      · exact Or.inl (Or.inr ⟨hi, h, hcl c₂ h⟩)
      · exact Or.inr ⟨hi, h, hcl c₃ h⟩

/-- An edge of `Γ` misses `U(Γ')`, so it lies inside or outside a closed set with frontier in
`U(Γ')`. -/
theorem edge_subset_or_disjoint_of_radial (hrad : Γ.U ∩ Γ'.U = Γ.V) {Δ : Set S} (hΔ : IsClosed Δ)
    (hb : frontier Δ ⊆ Γ'.U) {e : Set S} (he : e ∈ Γ.E) : e ⊆ Δ ∨ Disjoint e Δ :=
  edge_subset_or_disjoint_of_normal_frontier hΔ (fun _ hx => hrad ▸ ⟨hx.2, hb hx.1⟩) he

/-- Three small closed sides with radial frontiers cannot cover the surface. -/
theorem not_cover_of_radial_frontiers (hT : IsPretangle Γ.toHypergraph θ T)
    (hrad : Γ.U ∩ Γ'.U = Γ.V)
    {Δ₁ Δ₂ Δ₃ : Set S} (c₁ : IsClosed Δ₁) (c₂ : IsClosed Δ₂) (c₃ : IsClosed Δ₃)
    (b₁ : frontier Δ₁ ⊆ Γ'.U) (b₂ : frontier Δ₂ ⊆ Γ'.U) (b₃ : frontier Δ₃ ⊆ Γ'.U)
    (m₁ : (Γ.inter Δ₁, Γ.interOutside Δ₁) ∈ T) (m₂ : (Γ.inter Δ₂, Γ.interOutside Δ₂) ∈ T)
    (m₃ : (Γ.inter Δ₃, Γ.interOutside Δ₃) ∈ T)
    (hcov : Δ₁ ∪ Δ₂ ∪ Δ₃ = univ) : False := by
  have normal {Δ : Set S} (h : frontier Δ ⊆ Γ'.U) : Γ.IsNormal (frontier Δ) :=
    fun _ hx => hrad ▸ ⟨hx.2, h hx.1⟩
  exact not_support_subset_of_normal_frontiers hT c₁ c₂ c₃
    (normal b₁) (normal b₂) (normal b₃) m₁ m₂ m₃ (hcov ▸ subset_univ _)

end GraphMinor.GM11
