/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.EdgeSides

/-!
# Regions and edges of a drawing in a closed surface

This file proves the facts on regions that Graph Minors XI uses without comment:

- a closed surface is locally connected, so regions are open (`region_isOpen`);
- if a region has a point of an edge `e` in its closure, then all of `e` is in its closure
  (`edge_subset_closure_of_incident`);
- every edge is incident with a region, and with at most two (`exists_region_incident`,
  `region_incident_two`);
- a region not incident with `e` is still a region after `e` is deleted
  (`region_deleteEdge_of_not_incident`).

The proofs use the two sides of an edge, `exists_edge_sides`.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A closed surface is locally connected, because its charts are open subsets of the plane. -/
theorem IsClosedSurface.locallyConnectedSpace (hS : IsClosedSurface S) :
    LocallyConnectedSpace S := by
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr fun x U hU => ?_
  obtain ⟨V, hV, hxV, ⟨h⟩⟩ := hS.2.2 x
  let P : Set OpenUnitDisc := {y | (h.symm y).1 ∈ interior U}
  have hP : IsOpen P :=
    isOpen_interior.preimage (continuous_subtype_val.comp h.symm.continuous)
  have hP' : IsOpen (Subtype.val '' P : Set EuclideanPlane) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap _ hP
  let c : OpenUnitDisc := h ⟨x, hxV⟩
  have hc : (c : EuclideanPlane) ∈ (Subtype.val '' P : Set EuclideanPlane) :=
    ⟨c, by simpa [P, c] using mem_interior_iff_mem_nhds.mpr hU, rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hP' _ hc
  let B : Set OpenUnitDisc := Subtype.val ⁻¹' Metric.ball (c : EuclideanPlane) δ
  have hBsub : Metric.ball (c : EuclideanPlane) δ ⊆ OpenUnitDisc := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := hball hy
    exact z.2
  have hBconn : IsPreconnected B := by
    refine (IsInducing.subtypeVal :
      IsInducing (Subtype.val : OpenUnitDisc → EuclideanPlane)).isPreconnected_image.mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hBsub]
    exact (convex_ball _ _).isPreconnected
  let f : OpenUnitDisc → S := fun y => (h.symm y).1
  have hf : Continuous f := continuous_subtype_val.comp h.symm.continuous
  have hEq : f '' B = Subtype.val '' ((fun y : V => (h y : EuclideanPlane)) ⁻¹'
      Metric.ball (c : EuclideanPlane) δ) := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨h.symm y, ?_, rfl⟩
      simp only [mem_preimage, Homeomorph.apply_symm_apply]
      exact hy
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h y, hy, by simp [f]⟩
  refine ⟨f '' B, ?_, ?_, ?_, ⟨⟨f c, c, by simp [B, hδ], rfl⟩, hBconn.image _ hf.continuousOn⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hball hy
    have : z = y := Subtype.ext hzy
    subst this
    exact interior_subset hz
  · rw [hEq]
    exact hV.isOpenEmbedding_subtypeVal.isOpenMap _
      (Metric.isOpen_ball.preimage (continuous_subtype_val.comp h.continuous))
  · exact ⟨c, by simp [B, hδ], by simp [f, c]⟩

variable (Γ : Drawing S)

theorem mem_R_iff {r : Set S} :
    r ∈ Γ.R ↔ ∃ x, x ∉ Γ.U ∧ r = connectedComponentIn (univ \ Γ.U) x := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨mem_univ _, hx⟩, rfl⟩

variable {Γ}

theorem region_subset {r : Set S} (hr : r ∈ Γ.R) : r ⊆ Γ.Uᶜ := by
  obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp hr
  exact fun y hy => (connectedComponentIn_subset _ _ hy).2

theorem region_isPreconnected {r : Set S} (hr : r ∈ Γ.R) : IsPreconnected r := by
  obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp hr
  exact isPreconnected_connectedComponentIn

theorem region_nonempty {r : Set S} (hr : r ∈ Γ.R) : r.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := (mem_R_iff Γ).mp hr
  exact ⟨x, mem_connectedComponentIn ⟨mem_univ _, hx⟩⟩

theorem region_isOpen [LocallyConnectedSpace S] {r : Set S} (hr : r ∈ Γ.R) : IsOpen r := by
  obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp hr
  have : IsOpen (univ \ Γ.U) := isOpen_univ.sdiff Γ.isClosed_U
  exact this.connectedComponentIn

/-- Two regions with a common point are equal. -/
theorem region_eq_of_mem {r r' : Set S} (hr : r ∈ Γ.R) (hr' : r' ∈ Γ.R) {x : S} (hx : x ∈ r)
    (hx' : x ∈ r') : r = r' := by
  obtain ⟨y, -, rfl⟩ := (mem_R_iff Γ).mp hr
  obtain ⟨z, -, rfl⟩ := (mem_R_iff Γ).mp hr'
  rw [connectedComponentIn_eq hx, connectedComponentIn_eq hx']

/-- A connected set that avoids `U(Γ)` and meets a region lies in it. -/
theorem subset_region {r A : Set S} (hr : r ∈ Γ.R) (hA : IsPreconnected A)
    (hdis : Disjoint A Γ.U) {x : S} (hxA : x ∈ A) (hxr : x ∈ r) : A ⊆ r := by
  obtain ⟨y, -, rfl⟩ := (mem_R_iff Γ).mp hr
  rw [connectedComponentIn_eq hxr]
  exact hA.subset_connectedComponentIn hxA fun z hz => ⟨mem_univ _, disjoint_left.mp hdis hz⟩

/-- The region containing a point off `U(Γ)`. -/
theorem exists_region_of_notMem {x : S} (hx : x ∉ Γ.U) : ∃ r ∈ Γ.R, x ∈ r :=
  ⟨_, (mem_R_iff Γ).mpr ⟨x, hx, rfl⟩, mem_connectedComponentIn ⟨mem_univ _, hx⟩⟩

/-- The closure of a region adds only points of `U(Γ)`. -/
theorem closure_region_subset [LocallyConnectedSpace S] {r : Set S} (hr : r ∈ Γ.R) :
    closure r ⊆ r ∪ Γ.U := by
  intro y hy
  by_cases hyU : y ∈ Γ.U
  · exact Or.inr hyU
  obtain ⟨r', hr', hyr'⟩ := exists_region_of_notMem hyU
  obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hy r' (region_isOpen hr') hyr'
  rw [region_eq_of_mem hr hr' hz hz']
  exact Or.inl hyr'

/-- If a region has a point of an edge in its closure then all of the edge is in its closure. The
set of such points is open in `e` by the two sides of an edge, and `e` is connected. -/
theorem edge_subset_closure_of_incident (hS : IsClosedSurface S)
    {e r : Set S} (he : e ∈ Γ.E) (hr : r ∈ Γ.R)
    (hinc : (e ∩ closure r).Nonempty) : e ⊆ closure r := by
  have : T2Space S := hS.2.1
  have hstep : ∀ p ∈ e ∩ closure r, ∃ W : Set S, IsOpen W ∧ p ∈ W ∧ e ∩ W ⊆ closure r := by
    rintro p ⟨hpe, hpr⟩
    obtain ⟨W, A₁, A₂, hW, hpW, -, hsub, h₁, h₂, d₁, d₂, c₁, c₂⟩ := exists_edge_sides hS Γ he hpe
    refine ⟨W, hW, hpW, ?_⟩
    obtain ⟨x, hxW, hxr⟩ := mem_closure_iff.mp hpr W hW hpW
    have hxU : x ∉ Γ.U := region_subset hr hxr
    rcases hsub ⟨hxW, hxU⟩ with hx | hx
    · exact c₁.trans (closure_mono (subset_region hr h₁ d₁ hx hxr))
    · exact c₂.trans (closure_mono (subset_region hr h₂ d₂ hx hxr))
  choose! W hWo hpW hWs using hstep
  let O : Set S := ⋃ p ∈ e ∩ closure r, W p
  have hO : IsOpen O := isOpen_biUnion fun p hp => hWo p hp
  by_contra hcon
  obtain ⟨z, hze, hzr⟩ := not_subset.mp hcon
  have hconn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have hcov : e ⊆ O ∪ (closure r)ᶜ := by
    intro y hy
    by_cases hyr : y ∈ closure r
    · exact Or.inl (mem_iUnion₂.mpr ⟨y, ⟨hy, hyr⟩, hpW y ⟨hy, hyr⟩⟩)
    · exact Or.inr hyr
  obtain ⟨p, hp⟩ := hinc
  obtain ⟨y, hye, hyO, hyr⟩ := hconn O (closure r)ᶜ hO isClosed_closure.isOpen_compl hcov
    ⟨p, hp.1, mem_iUnion₂.mpr ⟨p, hp, hpW p hp⟩⟩ ⟨z, hze, hzr⟩
  obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hyO
  exact hyr (hWs q hq ⟨hye, hyq⟩)

/-- Every edge is incident with a region. -/
theorem exists_region_incident (hS : IsClosedSurface S)
    {e : Set S} (he : e ∈ Γ.E) :
    ∃ r ∈ Γ.R, e ⊆ closure r := by
  have : T2Space S := hS.2.1
  obtain ⟨p, hp⟩ := he.1
  obtain ⟨W, A₁, A₂, -, hpW, -, -, h₁, -, d₁, -, c₁, -⟩ := exists_edge_sides hS Γ he hp
  have hne : A₁.Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have := c₁ ⟨hp, hpW⟩
    rw [hcon, closure_empty] at this
    exact this
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp d₁ hx)
  refine ⟨r, hr, edge_subset_closure_of_incident hS he hr ⟨p, hp, ?_⟩⟩
  exact closure_mono (subset_region hr h₁ d₁ hx hxr) (c₁ ⟨hp, hpW⟩)

/-- An edge is incident with at most two regions: of three such regions, two are equal. -/
theorem region_incident_two (hS : IsClosedSurface S)
    {e r₁ r₂ r₃ : Set S} (he : e ∈ Γ.E) (h₁ : r₁ ∈ Γ.R) (h₂ : r₂ ∈ Γ.R)
    (h₃ : r₃ ∈ Γ.R) (i₁ : e ⊆ closure r₁) (i₂ : e ⊆ closure r₂) (i₃ : e ⊆ closure r₃) :
    r₁ = r₂ ∨ r₁ = r₃ ∨ r₂ = r₃ := by
  have : T2Space S := hS.2.1
  obtain ⟨p, hp⟩ := he.1
  obtain ⟨W, A₁, A₂, hW, hpW, -, hsub, c₁, c₂, d₁, d₂, -, -⟩ := exists_edge_sides hS Γ he hp
  have hside : ∀ r ∈ Γ.R, e ⊆ closure r → (∃ x ∈ A₁, x ∈ r) ∨ ∃ x ∈ A₂, x ∈ r := by
    intro r hr hi
    obtain ⟨x, hxW, hxr⟩ := mem_closure_iff.mp (hi hp) W hW hpW
    rcases hsub ⟨hxW, region_subset hr hxr⟩ with hx | hx
    · exact Or.inl ⟨x, hx, hxr⟩
    · exact Or.inr ⟨x, hx, hxr⟩
  have hsame : ∀ {A r r' : Set S}, IsPreconnected A → Disjoint A Γ.U → r ∈ Γ.R → r' ∈ Γ.R →
      (∃ x ∈ A, x ∈ r) → (∃ x ∈ A, x ∈ r') → r = r' := by
    rintro A r r' hA hd hr hr' ⟨x, hxA, hxr⟩ ⟨y, hyA, hyr⟩
    exact region_eq_of_mem hr hr' (subset_region hr hA hd hxA hxr hyA) hyr
  rcases hside r₁ h₁ i₁ with a | a <;> rcases hside r₂ h₂ i₂ with b | b <;>
    rcases hside r₃ h₃ i₃ with c | c
  · exact Or.inl (hsame c₁ d₁ h₁ h₂ a b)
  · exact Or.inl (hsame c₁ d₁ h₁ h₂ a b)
  · exact Or.inr (Or.inl (hsame c₁ d₁ h₁ h₃ a c))
  · exact Or.inr (Or.inr (hsame c₂ d₂ h₂ h₃ b c))
  · exact Or.inr (Or.inr (hsame c₁ d₁ h₂ h₃ b c))
  · exact Or.inr (Or.inl (hsame c₂ d₂ h₁ h₃ a c))
  · exact Or.inl (hsame c₂ d₂ h₁ h₂ a b)
  · exact Or.inl (hsame c₂ d₂ h₁ h₂ a b)

end GraphMinor.GM11
