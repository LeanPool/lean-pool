/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Separate
public import LeanPool.GraphMinor.GM11.RegionCount
public import LeanPool.GraphMinor.GM11.PaintingRegions
public import LeanPool.GraphMinor.Surface.Disc

/-!
# The outside of a set in a sphere

Let `Q` be a closed connected set in a sphere, and `D` a drawing with `U(D) = bd(Q)` whose `O`-arcs
bound
discs in `Q`. Then the complement of `Q` is a region of `D` and an open disc, and `D` is 2-cell
(`sphere_outside`). This gives the walk around `Q` by `exists_region_walk`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- A connected set that misses an `O`-arc in a sphere misses one of the two discs that the arc
bounds. -/
theorem exists_disc_missing (hS : IsClosedSurface S) (hsph : IsSphere S) {F T : Set S}
  (hF : IsOArc F)
    (hT : IsPreconnected T) (hTF : Disjoint T F) : ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F
      ∧ Disjoint Δ T := by
  have hT2 : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, -⟩ := sphere_disc S hsph F hF
  have hint₁ := IsClosedDisc.isOpen_discInt hman hΔ₁
  have hint₂ := IsClosedDisc.isOpen_discInt hman hΔ₂
  have hdint : Disjoint (discInt Δ₁) (discInt Δ₂) := by
    refine disjoint_left.mpr ?_
    rintro x ⟨h₁, h₂⟩ ⟨h₃, -⟩
    exact h₂ (by
      rw [hb₁, ← hcap]
      exact ⟨h₁, h₃⟩)
  have hcover : T ⊆ discInt Δ₁ ∪ discInt Δ₂ := by
    intro x hx
    have hxF : x ∉ F := disjoint_left.mp hTF hx
    have hxu : x ∈ Δ₁ ∪ Δ₂ := hcup ▸ mem_univ x
    rcases hxu with h | h
    · exact Or.inl ⟨h, by rwa [hb₁]⟩
    · exact Or.inr ⟨h, by rwa [hb₂]⟩
  rcases hT.subset_or_subset hint₁ hint₂ hdint hcover with h | h
  · refine ⟨Δ₂, hΔ₂, hb₂, disjoint_left.mpr fun x hx hxT => ?_⟩
    have h₁ := h hxT
    exact h₁.2 (by
      rw [hb₁, ← hcap]
      exact ⟨h₁.1, hx⟩)
  · refine ⟨Δ₁, hΔ₁, hb₁, disjoint_left.mpr fun x hx hxT => ?_⟩
    have h₁ := h hxT
    exact h₁.2 (by
      rw [hb₂, ← hcap]
      exact ⟨hx, h₁.1⟩)

/-- **The outside of a closed connected set `Q` in a sphere.** -/
theorem sphere_outside (hS : IsClosedSurface S) (hsph : IsSphere S) {Q : Set S} (hQc : IsClosed Q)
    (hQp : IsPreconnected Q) (hQne : Q.Nonempty) (hQu : Q ≠ univ) {D : Drawing S} (hU : D.U
      = frontier Q)
    (hdisc : ∀ F, IsOArc F → F ⊆ D.U → ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ Q ∧ discBd Δ = F) :
    Qᶜ ∈ D.R ∧ IsOpenDisc Qᶜ ∧ (PaintingOrDrawing.drawing D).IsTwoCell := by
  have hT2 : T2Space S := hS.2.1
  have hK : CompactSpace S := hS.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hUQ : D.U ⊆ Q := by
    rw [hU]
    exact hQc.frontier_subset
  obtain ⟨a, ha⟩ : ∃ a, a ∉ Q := by
    by_contra h
    push Not at h
    exact hQu (eq_univ_of_forall h)
  have haU : a ∉ D.U := fun h => ha (hUQ h)
  obtain ⟨p, hp, hap⟩ := exists_region_of_notMem haU
  have hsub : Qᶜ ⊆ p := by
    intro b hb
    obtain ⟨r, hr, har, hbr⟩ := same_region_of_discs hS hsph ha hb _ D rfl hUQ hdisc
    obtain rfl := region_eq_of_mem hr hp har hap
    exact hbr
  have hpsub : p ⊆ Qᶜ := by
    have hdis : p ⊆ interior Q ∪ Qᶜ := by
      intro x hx
      by_cases hxQ : x ∈ Q
      · refine Or.inl ?_
        by_contra hint
        exact region_subset hp hx (hU ▸ (⟨subset_closure hxQ, hint⟩ : x ∈ frontier Q))
      · exact Or.inr hxQ
    have hdj : Disjoint (interior Q) Qᶜ :=
      disjoint_left.mpr fun x hx h => h (interior_subset hx)
    rcases (region_isPreconnected hp).subset_or_subset isOpen_interior hQc.isOpen_compl hdj hdis
      with h | h
    · exact (ha (interior_subset (h hap))).elim
    · exact h
  have hpeq : p = Qᶜ := subset_antisymm hpsub hsub
  have hreg : Qᶜ ∈ D.R := hpeq ▸ hp
  have hcompl : IsConnected Qᶜ := ⟨⟨a, ha⟩, hpeq ▸ region_isPreconnected hp⟩
  have hopen : ∀ {Y : Set S}, IsConnected Y → IsOpen Y → Y ≠ univ →
      (∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F) →
      IsOpenDisc Y := by
    intro Y h₁ h₂ h₃ h₄
    rcases open_disc S Y hS inferInstance h₁ h₂ h₄ with h | h
    · exact (h₃ h.2).elim
    · exact h
  have hdiscQ : IsOpenDisc Qᶜ := by
    refine hopen hcompl hQc.isOpen_compl (fun h => ?_) fun F hF hO => ?_
    · obtain ⟨x, hx⟩ := hQne
      exact (h ▸ mem_univ x : x ∈ Qᶜ) hx
    · obtain ⟨Δ, h₁, h₂, h₃⟩ := exists_disc_missing hS hsph hO hQp
        (disjoint_left.mpr fun x hx hxF => hF hxF hx)
      exact ⟨Δ, fun x hx hxQ => disjoint_left.mp h₃ hx hxQ, h₁, h₂⟩
  have hfr : IsPreconnected D.U := by
    rw [hU, ← frontier_compl]
    exact isPreconnected_frontier hdiscQ
  have hUne : D.U.Nonempty := by
    rw [hU]
    exact nonempty_frontier_iff.mpr ⟨hQne, fun h => hQu h⟩
  refine ⟨hreg, hdiscQ, inferInstance, fun q hq => ?_⟩
  have hq' : q ∈ D.R := hq
  refine hopen ⟨region_nonempty hq', region_isPreconnected hq'⟩ (region_isOpen hq') (fun h => ?_)
    fun F hF hO => ?_
  · obtain ⟨x, hx⟩ := hUne
    exact region_subset hq' (h ▸ mem_univ x) hx
  · obtain ⟨Δ, h₁, h₂, h₃⟩ := exists_disc_missing hS hsph hO hfr
      (disjoint_left.mpr fun x hx hxF => region_subset hq' (hF hxF) hx)
    obtain ⟨z, hz⟩ : F.Nonempty := by
      obtain ⟨φ⟩ := hO
      exact ⟨(φ 1).1, (φ 1).2⟩
    have hzΔ : z ∈ Δ := discBd_subset Δ (h₂ ▸ hz)
    refine ⟨Δ, subset_region hq' (IsClosedDisc.isPathConnected h₁).isConnected.isPreconnected h₃
      hzΔ (hF hz), h₁, h₂⟩

end GraphMinor.GM11
