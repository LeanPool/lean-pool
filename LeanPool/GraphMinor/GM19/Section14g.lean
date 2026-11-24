/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14f
public import LeanPool.GraphMinor.GM19.FragmentOuter

/-!
# Graph Minors XIX, Section 14: the arm of a disc

A disc of `Σ̂` bounded by a circuit of `Γ*`, with some further vertices of `Γ` outside it, gives a
separation of `Γ`. The tools here show that it
lies in `𝒯`, and how a distinction compares with it. These are the steps of the claim (2) in the
proof of (14.1).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ}

/-- The part of `Γ` in `Δ`, with the vertices of `X` added. -/
def partPlus (D : TangleDatum cap χ) (Δ X : Set Shat) : Hypergraph S (Set S) := D.Γ.restrict
  (cap.emb ⁻¹' (Δ ∪ X))

omit [T2Space S] [T2Space Shat] in
theorem part_le_plus (D : TangleDatum cap χ) (Δ X : Set Shat) : partIn cap D.Γ Δ ≤ D.partPlus Δ X
  := by
  have : ConnectedSpace Shat := cap.connected
  exact part_mono subset_union_left

omit [T2Space S] [T2Space Shat] in
theorem edge_mem_plus_iff {Δ X : Set Shat} (hX : X ⊆ cap.emb '' D.Γ.V)
  (hΔ : IsClosed Δ) {e : Set S} : e ∈ (D.partPlus Δ X).edgeSet ↔ e ∈ (partIn cap D.Γ Δ).edgeSet
    := by
  constructor
  · rintro ⟨he, hs, ht⟩
    have hsub : e ⊆ cap.emb ⁻¹' Δ := fun z hz ↦ by
      refine (hs hz).resolve_right fun hzX ↦ ?_
      obtain ⟨y, hy, hyz⟩ := hX hzX
      have hzV : z ∈ D.Γ.V := cap.isEmbedding.injective hyz ▸ hy
      exact (he.2.1 hz).2 hzV
    have hcl : IsClosed (cap.emb ⁻¹' Δ) := hΔ.preimage cap.isEmbedding.continuous
    refine ⟨he, hsub, fun z hz ↦ ?_⟩
    exact closure_minimal hsub hcl hz.1.1
  · exact fun he ↦ (D.part_le_plus Δ X).edgeSet_subset he

theorem sep_plus {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G) {Δ X : Set Shat}
  (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = F.U) (hX : X ⊆ cap.emb '' D.Γ.V)
    : D.Γ.toHypergraph.IsSeparation (D.partPlus Δ X)
      (partIn cap D.Γ (closure Δᶜ)) := by
  have hT := cap.isClosedSurface
  have hs := (disc_facts χ.isSurface D.P.fits.internally_three_connected D.rad hF hΔ hbd).1
  have hl : D.partPlus Δ X ≤ D.Γ.toHypergraph := D.Γ.restrict_le _
  have hr : partIn cap D.Γ (closure Δᶜ) ≤ D.Γ.toHypergraph := D.Γ.restrict_le _
  have hl₀ : partIn cap D.Γ Δ ≤ D.Γ.toHypergraph := D.Γ.restrict_le _
  rw [isSeparation_iff_of_le hl hr]
  replace hs : D.Γ.toHypergraph.IsSeparation (partIn cap D.Γ Δ) (partIn cap D.Γ (closure Δᶜ)) := hs
  rw [isSeparation_iff_of_le hl₀ hr] at hs
  obtain ⟨h₁, h₂, h₃⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · apply subset_antisymm
    · exact union_subset hl.vertexSet_subset hr.vertexSet_subset
    · intro v hv
      have := h₁ ▸ hv
      rcases this with h | h
      · exact .inl ((D.part_le_plus Δ X).vertexSet_subset h)
      · exact .inr h
  · have : (D.partPlus Δ X).edgeSet = (partIn cap D.Γ Δ).edgeSet := Set.ext fun e ↦
      edge_mem_plus_iff hX hΔ.isClosed
    rw [this]
    exact h₂
  · have : (D.partPlus Δ X).edgeSet = (partIn cap D.Γ Δ).edgeSet := Set.ext fun e ↦
      edge_mem_plus_iff hX hΔ.isClosed
    rw [this]
    exact h₃

omit [T2Space S] [T2Space Shat] in
/-- A separation with the same first part up to some vertices is on the same side of `𝒯`. -/
theorem plus_mem_of_mem {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ord' : ℕ}
  (h𝒯' : IsTangle D.Γ.toHypergraph ord' 𝒯')
    {A A₀ B : Hypergraph S (Set S)} (hA : D.Γ.toHypergraph.IsSeparation A B)
      (hA₀ : D.Γ.toHypergraph.IsSeparation A₀ B)
    (hord : Hypergraph.separationOrder A B < ord') (hm : (A₀, B) ∈ 𝒯') : (A, B) ∈ 𝒯' := by
  refine (h𝒯'.axiom1 hA hord).resolve_right fun hn ↦ ?_
  refine h𝒯'.axiom2 hm hn hn ?_
  rw [GM10.union_assoc, GM10.union_self]
  exact hA₀.union_eq

omit [T2Space S] [T2Space Shat] in
/-- The first part may lose some vertices and stay on the same side, seen from the other tangle. -/
theorem part_mem_of_plus_mem {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ord' : ℕ}
  (h𝒯' : IsTangle D.Γ.toHypergraph ord' 𝒯')
    {A A₀ B : Hypergraph S (Set S)} (hA₀ : D.Γ.toHypergraph.IsSeparation A₀ B)
      (hord : Hypergraph.separationOrder A₀ B < ord') (hm : (B, A) ∈ 𝒯') : (B, A₀) ∈ 𝒯' := by
  refine (h𝒯'.axiom1 hA₀ hord).resolve_left fun hn ↦ ?_
  refine h𝒯'.axiom2 hn hm hm ?_
  rw [GM10.union_assoc, GM10.union_self]
  exact hA₀.union_eq

/-- The `(𝒯, 𝒯')`-distinction is the inside of an enclave around `𝒯'`, when a circuit of `Γ*` with
small inside separates them. -/
theorem exists_enclave_of_distinction {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S
  (Set S))} (h𝒯' : IsTangle D.Γ.toHypergraph ord' 𝒯') {F : Drawing Shat} {Δ : Set Shat}
    (hins : IsInsOf D.rad D.ord D.𝒯 F Δ) (hm : (partIn cap D.Γ (closure Δᶜ), partIn cap D.Γ Δ) ∈
      𝒯') {C B : Hypergraph S (Set S)}
    (hd : IsDistinction D.tb.lambdaOrder D.𝒯 𝒯' C B) :
    ∃ F', IsEnclaveAround D.tb D.ord ord' D.𝒯 𝒯' F' ∧ F'.E.ncard ≤ F.E.ncard ∧ C = partIn cap D.Γ
      (D.ins F') ∧ B = partIn cap D.Γ (closure (D.ins F')ᶜ) := by
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  have hle := (N1_le_of_lambda_le D.tb (hd.2 ⟨hins.2.2.2.2, hm⟩)).1
  simp only [TieBreaker.N1] at hle
  have hord := disc_order hS h3 D.rad hins.1 hins.2.2.1 hins.2.2.2.1
  have hlt : Hypergraph.separationOrder C B < tangleRep D.rad D.ord D.𝒯 := by
    have h₁ := hins.2.1
    have h₂ : Hypergraph.separationOrder (partIn cap D.P.Γ Δ) (partIn cap D.P.Γ (closure Δᶜ)) <
      tangleRep D.rad D.ord D.𝒯 := by omega
    exact lt_of_le_of_lt hle h₂
  obtain ⟨F', Δ', hins', rfl, rfl⟩ := theorem_8_4_proof hS h3 D.tb D.isTangle h𝒯' hd hlt
  obtain rfl := D.eq_ins_of_isInsOf hins'
  exact ⟨F', ⟨h𝒯', hins'.1, hins'.2.1, _, hins', hd⟩, enclave_card_le hS h3 D.tb hins' hd hins hm,
    rfl, rfl⟩

omit [T2Space S] [T2Space Shat] in
/-- If the inside of the enclave is in `Δ`, then the distinction is as (14.1) needs it. -/
theorem le_of_ins_subset {Δ Δ' X : Set Shat} (h : Δ' ⊆ Δ) : partIn cap D.Γ Δ' ≤ D.partPlus Δ X
  ∧ partIn cap D.Γ (closure Δᶜ) ≤ partIn cap D.Γ (closure Δ'ᶜ) := by
  have : ConnectedSpace Shat := cap.connected
  refine ⟨(part_mono h).trans (D.part_le_plus Δ X), part_mono (closure_mono
    (compl_subset_compl.mpr h))⟩

omit [T2Space S] [T2Space Shat] in
/-- The vertices of the separation of `Δ` with `X`. -/
theorem plus_inter_V {Δ X : Set Shat} (hΔ : IsClosedDisc Δ) (hoff : Disjoint X
  (discInt Δ)) {v : S} :
    v ∈ (D.partPlus Δ X ∩ partIn cap D.Γ (closure Δᶜ)).vertexSet ↔ v ∈ D.Γ.V
      ∧ cap.emb v ∈ discBd Δ ∪ X := by
  have hT := cap.isClosedSurface
  rw [GM10.inter_vertexSet]
  change (v ∈ D.Γ.V ∧ cap.emb v ∈ Δ ∪ X) ∧ (v ∈ D.Γ.V ∧ cap.emb v ∈ closure Δᶜ) ↔ _
  rw [closure_compl_disc hT hΔ]
  constructor
  · rintro ⟨⟨hv, h | h⟩, -, h'⟩
    · exact ⟨hv, .inl (by_contra fun hn ↦ h' ⟨h, hn⟩)⟩
    · exact ⟨hv, .inr h⟩
  · rintro ⟨hv, h | h⟩
    · exact ⟨⟨hv, .inl (Surface.discBd_subset _ h)⟩, hv, fun h' ↦ h'.2 h⟩
    · exact ⟨⟨hv, .inr h⟩, hv, fun h' ↦ disjoint_left.mp hoff h h'⟩

end TangleDatum

end GraphMinor.GM19
