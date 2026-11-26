/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualContractDefs

/-!
# A line dual, and the collapse of a star

Facts for `exists_contracted_dual`. Let `Γ₁` be made from the lines of `IsDualLines`. Each edge `e`
of
`Γ` meets `Γ₁` only at `m e` (`inter_dual`), where it meets its dual edge `dualEdge`.

A region of `Γ₁` with `v` off its closure is a region of `Γ₁ \ v` (`region_mem_delete`).
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The union of two lines of `IsDualLines`, less the hubs. -/
def dualEdge (h : Set S × Bool → S) (ℓ : Set S × Bool → I → S) (e : Set S) : Set S :=
  (range (ℓ (e, true)) ∪ range (ℓ (e, false))) \ {h (e, true), h (e, false)}

omit [ConnectedSpace S] in
/-- See the module docstring. -/
theorem region_mem_delete (hS : IsClosedSurface S) {G : Drawing S} {v : S} {t : Set S}
  (ht : t ∈ G.R)
    (hv : v ∉ closure t) : t ∈ (deleteVertices G {v}).R := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  set G' := deleteVertices G {v} with hG'
  have hsub : G'.U ⊆ G.U := (deleteVertices_isSubdrawing G {v}).U_subset
  have hcl : closure t ⊆ t ∪ G'.U := by
    intro y hy
    rcases closure_region_subset ht hy with h' | h'
    · exact Or.inl h'
    by_cases hyV : y ∈ G.V
    · have hyv : y ≠ v := fun h'' => hv (h'' ▸ hy)
      have : y ∈ G'.V := by
        rw [hG', deleteVertices_V]
        exact ⟨hyV, hyv⟩
      exact Or.inr (G'.V_subset_U this)
    · obtain ⟨g, hg, hyg⟩ := G.exists_edge_of_mem h' hyV
      have hgt : g ⊆ closure t := edge_subset_closure_of_incident hS hg ht ⟨y, hyg, hy⟩
      have hgG' : g ∈ G'.E := by
        rw [hG', deleteVertices_E]
        refine ⟨hg, disjoint_left.mpr fun z hz hzv => hv ?_⟩
        have hzv' : z = v := hzv
        exact hzv' ▸ closure_minimal hgt isClosed_closure hz.1
      exact Or.inr (G'.closure_subset_U hgG' (subset_closure hyg))
  have hclosed : IsClosed (t ∪ G'.U) := by
    refine isClosed_of_closure_subset ?_
    rw [closure_union, G'.isClosed_U.closure_eq]
    exact union_subset (hcl.trans Subset.rfl) subset_union_right
  have hdis : Disjoint t G'.U := disjoint_left.mpr fun z hz hz' => region_subset ht hz (hsub hz')
  refine mem_R_of_split (C' := (t ∪ G'.U)ᶜ) (region_isOpen ht) hclosed.isOpen_compl
    (region_nonempty ht) (region_isPreconnected ht) (disjoint_left.mpr fun z hz h' => h'
      (Or.inl hz)) ?_
  ext z
  constructor
  · rintro (hz | hz) hzU
    · exact disjoint_left.mp hdis hz hzU
    · exact hz (Or.inr hzU)
  · intro hz
    by_cases hzt : z ∈ t
    · exact Or.inl hzt
    · refine Or.inr ?_
      rintro (h' | h')
      · exact hzt h'
      · exact hz h'

namespace IsDualLines

variable {Γ K D₀ Γ₁ : Drawing S} {hrad : PreRad (PaintingOrDrawing.drawing Γ) K}
  {A B : Set S → Set S} {m x y : Set S → S} {φ : Set S × Bool → Set S} {h : Set S × Bool → S}
  {ℓ : Set S × Bool → I → S} (hL : IsDualLines hrad D₀ A B m x y φ h ℓ)
  (h₁U : Γ₁.U = (K.V \ Γ.V) ∪ ⋃ e ∈ Γ.E, (range (ℓ (e, true)) ∪ range (ℓ (e, false))))

include hL

omit [ConnectedSpace S] in
theorem hub_mem_line {e : Set S} (he : e ∈ Γ.E) (b : Bool) : h (e, b) ∈ range (ℓ (e, b)) :=
  line_right_mem (hL.isLine he b)

omit [ConnectedSpace S] in
theorem m_mem_line {e : Set S} (he : e ∈ Γ.E) (b : Bool) : m e ∈ range (ℓ (e, b)) :=
  line_left_mem (hL.isLine he b)

omit [ConnectedSpace S] in
theorem m_mem_dualEdge {e : Set S} (he : e ∈ Γ.E) : m e ∈ dualEdge h ℓ e := by
  refine ⟨Or.inl (hL.m_mem_line he true), ?_⟩
  rintro (h' | h')
  · exact hL.hub_ne_m he he true h'.symm
  · exact hL.hub_ne_m he he false h'.symm

omit [T2Space S] [ConnectedSpace S] in
/-- A point of the dual edge is on a face beside `e` or is `m e`. -/
theorem mem_dualEdge {e : Set S} (he : e ∈ Γ.E) {z : S} (hz : z ∈ dualEdge h ℓ e) :
    (∃ b, z ∈ φ (e, b)) ∨ z = m e := by
  obtain ⟨hz | hz, hn⟩ := hz
  · rcases hL.mem_line he true hz with h₁ | h₁ | h₁
    · exact Or.inl ⟨true, h₁⟩
    · exact Or.inr h₁
    · exact absurd (Or.inl h₁) hn
  · rcases hL.mem_line he false hz with h₁ | h₁ | h₁
    · exact Or.inl ⟨false, h₁⟩
    · exact Or.inr h₁
    · exact absurd (Or.inr h₁) hn

omit [ConnectedSpace S] in
/-- The closure of the dual edge is the union of the two lines. -/
theorem closure_dualEdge {e : Set S} (he : e ∈ Γ.E) :
    closure (dualEdge h ℓ e) = range (ℓ (e, true)) ∪ range (ℓ (e, false)) := by
  have hsub : ∀ b, range (ℓ (e, b)) \ {m e, h (e, b)} ⊆ dualEdge h ℓ e := by
    rintro b z ⟨hz, hn⟩
    have hzf : z ∈ φ (e, b) := by
      rcases hL.mem_line he b hz with h₁ | h₁ | h₁
      · exact h₁
      · exact absurd (Or.inl h₁) hn
      · exact absurd (Or.inr h₁) hn
    refine ⟨?_, ?_⟩
    · cases b
      · exact Or.inr hz
      · exact Or.inl hz
    · rintro (h₁ | h₁)
      · exact (hL.face_off he b hzf).2 (h₁ ▸ hL.hub_K he true)
      · exact (hL.face_off he b hzf).2 (h₁ ▸ hL.hub_K he false)
  apply subset_antisymm
  · refine closure_minimal sdiff_subset ?_
    exact (isCompact_range (hL.cont e he true)).isClosed.union
      (isCompact_range (hL.cont e he false)).isClosed
  · refine union_subset ?_ ?_
    · have := closure_mono (hsub true)
      rwa [closure_sdiff_pair (hL.isLine he true)] at this
    · have := closure_mono (hsub false)
      rwa [closure_sdiff_pair (hL.isLine he false)] at this

omit [ConnectedSpace S] in
theorem dualEdge_inj {e e' : Set S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E)
    (heq : dualEdge h ℓ e = dualEdge h ℓ e') : e = e' := by
  have hm := hL.m_mem_dualEdge he
  rw [heq] at hm
  rcases hL.mem_dualEdge he' hm with ⟨b, hb⟩ | h₁
  · exact absurd (hL.m_U he) (hL.face_off he' b hb).1
  · exact hL.m_inj he he' h₁

include h₁U in
omit [T2Space S] [ConnectedSpace S] in
/-- An edge of `Γ` meets the dual only at `m e`. -/
theorem inter_dual {e : Set S} (he : e ∈ Γ.E) {z : S} (hz : z ∈ e) (hz' : z ∈ Γ₁.U) : z = m e := by
  have hzK : z ∉ K.U := disjoint_left.mp (edge_disjoint hrad he) hz
  have hzU : z ∈ Γ.U := Γ.closure_subset_U he (subset_closure hz)
  rw [h₁U] at hz'
  rcases hz' with hz' | hz'
  · exact absurd (K.V_subset_U hz'.1) hzK
  · obtain ⟨e', he', hz'⟩ := mem_iUnion₂.mp hz'
    have key : ∀ b, z ∈ range (ℓ (e', b)) → z = m e := by
      intro b hzb
      rcases hL.mem_line he' b hzb with h₁ | h₁ | h₁
      · exact absurd hzU (hL.face_off he' b h₁).1
      · obtain rfl := hL.m_inj he he' (Γ.edge_eq_of_mem he he' hz (h₁ ▸ hL.m_mem he') ▸ rfl)
        exact h₁
      · exact absurd (h₁ ▸ hzK) (fun h' => h' (hL.hub_K he' b))
    rcases hz' with hz' | hz'
    · exact key true hz'
    · exact key false hz'

end IsDualLines

end GraphMinor.GM12
